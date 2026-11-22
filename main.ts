// mend: applies an edit that an AI model wrote to a tree of text files (SPEC.md). Node 22, standard library alone;
// run it as `node main.ts [options] [PATCH]`.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

type Tier = 0 | 1 | 2;
const trail = (s: string): string => s.replace(/[ \t]+$/, '');
const both = (s: string): string => trail(s.replace(/^[\t ]+/, ''));
const lead = (s: string): string => /^[\t ]*/.exec(s)![0];
const eqAt = (t: Tier): ((a: string, b: string) => boolean) =>
  t === 0 ? (a, b) => a === b : t === 1 ? (a, b) => trail(a) === trail(b) : (a, b) => both(a) === both(b);

interface Piece {
  ctx: boolean;
  text: string;
  oi: number;
}

/** The positions at or after `from` where O occurs, at the first tier with one (section 5). */
function whereFrom(lines: string[], O: string[], from: number, strict: boolean): { tier: Tier; at: number[] } | null {
  const top: Tier = strict ? 0 : 2;
  for (let tier: Tier = 0; tier <= top; tier = (tier + 1) as Tier) {
    const eq = eqAt(tier);
    const at: number[] = [];
    for (let i = from; i + O.length <= lines.length; i += 1) {
      let ok = true;
      for (let k = 0; k < O.length && ok; k += 1) ok = eq(lines[i + k]!, O[k]!);
      if (ok) at.push(i);
    }
    if (at.length > 0) return { tier, at };
  }
  return null;
}

const where = (lines: string[], O: string[], strict: boolean): { tier: Tier; at: number[] } | null => whereFrom(lines, O, 0, strict);

function splitText(text: string): { br: string; lines: string[]; final: boolean } {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { br, lines, final };
}

function joinText(lines: string[], br: string, final: boolean): string {
  return lines.length === 0 ? '' : lines.join(br) + (final ? br : '');
}

/** N written for the match of O at pos: context as the file's own lines, at tier 2 the rest re-indented. */
function rewritten(fileLines: string[], pos: number, O: string[], N: Piece[], tier: Tier, strict: boolean): string[] {
  const out: string[] = [];
  const doIt = tier === 2 && !strict && O.length > 0;
  const F = doIt ? lead(fileLines[pos]!) : '';
  const P = doIt ? lead(O[0]!) : '';
  let oi = 0;
  for (const p of N) {
    if (p.ctx && p.oi >= 0) {
      out.push(fileLines[pos + p.oi]!);
      oi += 1;
      continue;
    }
    let t = p.text;
    if (doIt && t !== '' && t.trim() !== '' && t.startsWith(P)) t = F + t.slice(P.length);
    out.push(t);
  }
  return out;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

interface ULine {
  kind: 'ctx' | 'old' | 'new' | 'back';
  text: string;
  bare: boolean;
}
interface UHunk {
  a: number;
  body: ULine[];
}
interface USec {
  gitOld: string | null;
  gitNew: string | null;
  old: string | null;
  newp: string | null;
  sawPair: boolean;
  create: boolean;
  del: boolean;
  renameFrom: string | null;
  renameTo: string | null;
  hunks: UHunk[];
}

const gitPath = (l: string): { old: string; new: string } | null => {
  const rest = l.slice('diff --git '.length);
  if (!rest.startsWith('a/')) return null;
  const at = rest.lastIndexOf(' b/');
  return at < 0 ? null : { old: rest.slice(2, at), new: rest.slice(at + 3) };
};

const dashPath = (l: string): string | null => {
  let p = l.slice(4);
  const t = p.indexOf('\t');
  if (t >= 0) p = p.slice(0, t);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
};

const HUNK = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@(?: .*)?$/;

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const secs: USec[] = [];
  let cur: USec | null = null;
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const g = gitPath(l);
      if (g === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { gitOld: g.old, gitNew: g.new, old: null, newp: null, sawPair: false, create: false, del: false, renameFrom: null, renameTo: null, hunks: [] };
      secs.push(cur);
      i += 1;
      continue;
    }
    if (l.startsWith('--- ')) {
      const next = lines[i + 1] ?? '';
      if (next.startsWith('+++ ')) {
        if (cur === null || cur.hunks.length > 0 || cur.sawPair) {
          cur = { gitOld: null, gitNew: null, old: null, newp: null, sawPair: false, create: false, del: false, renameFrom: null, renameTo: null, hunks: [] };
          secs.push(cur);
        }
        cur.sawPair = true;
        cur.old = dashPath(l);
        cur.newp = dashPath(next);
        i += 2;
        continue;
      }
      if (cur !== null && cur.hunks.length === 0) throw new Exit2(`error: parse ${i + 2}`);
      i += 1;
      continue;
    }
    if (l.startsWith('@@')) {
      const m = HUNK.exec(l);
      if (m === null || cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const body: ULine[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const b = lines[j]!;
        if (b.startsWith('diff --git ') || (b.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ '))) break;
        if (b === '') {
          body.push({ kind: 'ctx', text: '', bare: true });
          j += 1;
          continue;
        }
        const c = b[0]!;
        if (c === ' ' || c === '-' || c === '+') {
          body.push({ kind: c === ' ' ? 'ctx' : c === '-' ? 'old' : 'new', text: b.slice(1), bare: false });
          j += 1;
          continue;
        }
        if (c === '\\') {
          body.push({ kind: 'back', text: '', bare: false });
          j += 1;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1]!.bare) body.pop();
      cur.hunks.push({ a: Number(m[1]), body });
      i = j;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (l.startsWith('rename from ') && cur.renameFrom === null) cur.renameFrom = l.slice(12);
      else if (l.startsWith('rename to ') && cur.renameTo === null) cur.renameTo = l.slice(10);
      else if (l.startsWith('new file mode')) cur.create = true;
      else if (l.startsWith('deleted file mode')) cur.del = true;
    }
    i += 1;
  }
  return secs.map((sec) => unifiedSecEdit(sec, strict));
}

function applyHunks(before: string, sec: USec, strict: boolean, p: string): string {
  const { br, lines, final } = splitText(before);
  let d = 0;
  let fin = final;
  for (const h of sec.hunks) {
    const O: string[] = [];
    const N: Piece[] = [];
    const ctxAt: number[] = [];
    for (const b of h.body) {
      if (b.kind === 'ctx') {
        ctxAt.push(O.length);
        O.push(b.text);
        N.push({ ctx: true, text: b.text, oi: -1 });
      } else if (b.kind === 'old') O.push(b.text);
      else if (b.kind === 'new') N.push({ ctx: false, text: b.text, oi: -1 });
    }
    let ci = 0;
    for (const p of N) {
      if (p.ctx) {
        p.oi = ci < ctxAt.length ? ctxAt[ci]! : -1;
        ci += 1;
      }
    }
    let last = -1;
    for (let k = 0; k < h.body.length; k += 1) if (h.body[k]!.kind === 'ctx' || h.body[k]!.kind === 'new') last = k;
    const noNl = last >= 0 && last + 1 < h.body.length && h.body[last + 1]!.kind === 'back';
    if (O.length > 0) {
      const w = where(lines, O, strict);
      if (w === null) throw new Fail('no-match', p);
      const target = h.a - 1 + d;
      let at = w.at[0]!;
      for (const q of w.at) if (Math.abs(q - target) < Math.abs(at - target)) at = q;
      const nn = rewritten(lines, at, O, N, w.tier, strict);
      const atEnd = at + O.length === lines.length;
      lines.splice(at, O.length, ...nn);
      if (atEnd) fin = !noNl;
    } else {
      const at = Math.min(h.a + d, lines.length);
      const atEnd = at === lines.length;
      lines.splice(at, 0, ...N.map((x) => x.text));
      if (atEnd) fin = !noNl;
    }
    d += N.length - O.length;
  }
  return joinText(lines, br, fin);
}

function unifiedSecEdit(sec: USec, strict: boolean): Edit {
  return (tree) => {
    const oldRaw = sec.old ?? sec.renameFrom ?? sec.gitOld;
    const newRaw = sec.newp ?? sec.renameTo ?? sec.gitNew;
    if (oldRaw !== null && !safe(oldRaw)) throw new Fail('unsafe', oldRaw);
    if (newRaw !== null && !safe(newRaw)) throw new Fail('unsafe', newRaw);
    const isCreate = sec.create || oldRaw === null;
    const isDel = sec.del || newRaw === null;
    if (isCreate) {
      if (newRaw === null) return;
      if (tree.get(newRaw) !== null) throw new Fail('exists', newRaw);
      const out: string[] = [];
      let backed = false;
      for (const h of sec.hunks) {
        for (let k = 0; k < h.body.length; k += 1) {
          const b = h.body[k]!;
          if (b.kind !== 'new') continue;
          out.push(b.text);
          backed = k + 1 < h.body.length && h.body[k + 1]!.kind === 'back';
        }
      }
      tree.now.set(newRaw, out.length === 0 ? '' : out.join('\n') + (backed ? '' : '\n'));
      return;
    }
    if (isDel) {
      if (oldRaw === null) return;
      if (tree.get(oldRaw) === null) throw new Fail('missing', oldRaw);
      tree.now.set(oldRaw, null);
      return;
    }
    const p = oldRaw!;
    const before = tree.get(p);
    if (before === null) throw new Fail('missing', p);
    const text = applyHunks(before, sec, strict, p);
    if (newRaw !== null && newRaw !== p) {
      if (tree.get(newRaw) !== null) throw new Fail('exists', newRaw);
      tree.now.set(newRaw, text);
      tree.now.set(p, null);
      tree.moves.push([p, newRaw]);
    } else tree.now.set(p, text);
  };
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let lastPath: string | null = null;
  let prevEnd = -1;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const at = i;
    let path: string | null = null;
    for (let k = at - 1; k > prevEnd; k -= 1) {
      const c = lines[k]!.trim();
      if (c !== '' && !c.startsWith('```')) {
        path = c;
        break;
      }
    }
    if (path === null) path = lastPath;
    if (path === null) throw new Exit2(`error: parse ${at + 1}`);
    const old: string[] = [];
    let j = at + 1;
    while (j < lines.length && lines[j]!.trimEnd() !== '=======') {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') throw new Exit2(`error: parse ${at + 1}`);
      old.push(lines[j]!);
      j += 1;
    }
    if (j >= lines.length) throw new Exit2(`error: parse ${at + 1}`);
    const neu: string[] = [];
    j += 1;
    while (j < lines.length && lines[j]!.trimEnd() !== '>>>>>>> REPLACE') {
      neu.push(lines[j]!);
      j += 1;
    }
    if (j >= lines.length) throw new Exit2(`error: parse ${at + 1}`);
    edits.push(srEdit(path, old, neu, strict));
    lastPath = path;
    prevEnd = j;
    i = j + 1;
  }
  return edits;
}

function srEdit(path: string, old: string[], neu: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (old.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, neu.length === 0 ? '' : neu.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const { br, lines, final } = splitText(before);
    const w = where(lines, old, strict);
    if (w === null) throw new Fail('no-match', path);
    if (w.at.length > 1) throw new Fail('ambiguous', path);
    const nn = rewritten(lines, w.at[0]!, old, neu.map((t) => ({ ctx: false, text: t, oi: -1 })), w.tier, strict);
    lines.splice(w.at[0]!, old.length, ...nn);
    tree.now.set(path, joinText(lines, br, final));
  };
}

interface VChunk {
  anchor: string | null;
  body: { kind: 'ctx' | 'old' | 'new'; text: string }[];
  eof: boolean;
}

const V_MARKS = ['*** Add File: ', '*** Delete File: ', '*** Update File: '];

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let end = lines.length - 1;
  while (end >= 0 && blank(lines[end]!)) end -= 1;
  if (end < first || lines[end]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < end) {
    const l = lines[i]!;
    if (blank(l)) {
      i += 1;
      continue;
    }
    const mark = V_MARKS.find((m) => l.startsWith(m));
    if (mark === undefined) throw new Exit2(`error: parse ${i + 1}`);
    const path = l.slice(mark.length).trim();
    let j = i + 1;
    while (j < end && V_MARKS.every((m) => !lines[j]!.startsWith(m))) j += 1;
    if (mark === '*** Add File: ') {
      const raw = lines.slice(i + 1, j);
      while (raw.length > 0 && blank(raw[raw.length - 1]!)) raw.pop();
      const body: string[] = [];
      raw.forEach((b, k) => {
        if (b === '' || blank(b)) body.push('');
        else if (b.startsWith('+')) body.push(b.slice(1));
        else throw new Exit2(`error: parse ${i + 2 + k}`);
      });
      edits.push(v4aAdd(path, body));
    } else if (mark === '*** Delete File: ') {
      const bad = lines.slice(i + 1, j).findIndex((b) => !blank(b));
      if (bad >= 0) throw new Exit2(`error: parse ${i + 2 + bad}`);
      edits.push(v4aDelete(path));
    } else {
      let k = i + 1;
      let moveTo: string | null = null;
      if (k < end && lines[k]!.startsWith('*** Move to: ')) {
        moveTo = lines[k]!.slice(13).trim();
        k += 1;
      }
      const raw = lines.slice(k, j);
      while (raw.length > 0 && blank(raw[raw.length - 1]!)) raw.pop();
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      raw.forEach((b, r) => {
        const at = k + r + 1;
        if (b === '*** End of File') {
          if (cur !== null) {
            cur.eof = true;
            chunks.push(cur);
            cur = null;
          } else chunks.push({ anchor: null, body: [], eof: true });
          return;
        }
        if (b.startsWith('@@')) {
          if (cur !== null) chunks.push(cur);
          const a = b.slice(2).trim();
          cur = { anchor: a === '' ? null : a, body: [], eof: false };
          return;
        }
        const line = b === '' ? { kind: 'ctx' as const, text: '' } : b[0] === ' ' ? { kind: 'ctx' as const, text: b.slice(1) } : b[0] === '-' ? { kind: 'old' as const, text: b.slice(1) } : b[0] === '+' ? { kind: 'new' as const, text: b.slice(1) } : null;
        if (line === null) throw new Exit2(`error: parse ${at}`);
        if (cur === null) {
          if (chunks.length === 0) cur = { anchor: null, body: [], eof: false };
          else throw new Exit2(`error: parse ${at}`);
        }
        cur.body.push(line);
      });
      if (cur !== null) chunks.push(cur);
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${i + 1}`);
      edits.push(v4aUpdate(path, moveTo, chunks, strict));
    }
    i = j;
  }
  return edits;
}

function v4aAdd(path: string, body: string[]): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) !== null) throw new Fail('exists', path);
    tree.now.set(path, body.length === 0 ? '' : body.join('\n') + '\n');
  };
}

function v4aDelete(path: string): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) === null) throw new Fail('missing', path);
    tree.now.set(path, null);
  };
}

function v4aUpdate(path: string, moveTo: string | null, chunks: VChunk[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const { br, lines, final } = splitText(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        const w = whereFrom(lines, [ch.anchor], cursor, strict);
        if (w === null) throw new Fail('no-match', path);
        cursor = w.at[0]! + 1;
      }
      const O: string[] = [];
      const N: Piece[] = [];
      const ctxAt: number[] = [];
      for (const b of ch.body) {
        if (b.kind === 'ctx') {
          ctxAt.push(O.length);
          O.push(b.text);
          N.push({ ctx: true, text: b.text, oi: -1 });
        } else if (b.kind === 'old') O.push(b.text);
        else N.push({ ctx: false, text: b.text, oi: -1 });
      }
      let ci = 0;
      for (const p of N) {
        if (p.ctx) {
          p.oi = ci < ctxAt.length ? ctxAt[ci]! : -1;
          ci += 1;
        }
      }
      if (O.length > 0) {
        const w = whereFrom(lines, O, cursor, strict);
        let at = -1;
        for (const q of w === null ? [] : w.at) if (!ch.eof || q + O.length === lines.length) {
          at = q;
          break;
        }
        if (at < 0) throw new Fail('no-match', path);
        const nn = rewritten(lines, at, O, N, w!.tier, strict);
        lines.splice(at, O.length, ...nn);
        cursor = at + nn.length;
      } else {
        const at = ch.eof ? lines.length : Math.min(cursor, lines.length);
        lines.splice(at, 0, ...N.map((x) => x.text));
        cursor = at + N.length;
      }
    }
    const text = joinText(lines, br, final);
    if (moveTo !== null) {
      tree.now.set(moveTo, text);
      tree.now.set(path, null);
      tree.moves.push([path, moveTo]);
    } else tree.now.set(path, text);
  };
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const ls = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) ls.pop();
      if (line < 0 || line > ls.length) throw new Fail('no-match', p);
      ls.splice(line, 0, ...add);
      tree.now.set(p, ls.length === 0 ? '' : ls.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = kind === 'unified' ? unifiedEdits(lines, strict) : kind === 'search-replace' ? srEdits(lines, strict) : kind === 'v4a' ? v4aEdits(lines, strict) : jsonEdits(text, lines);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: { key: string; line: string; del?: string; put?: [string, string] }[] = [];
  const moved = new Set<string>();
  for (const [o, n] of tree.moves) {
    if (tree.original(o) !== null && (tree.now.get(o) ?? null) === null && tree.original(n) === null && (tree.now.get(n) ?? null) !== null) {
      rows.push({ key: n, line: `R ${o} -> ${n}`, del: o, put: [n, tree.now.get(n)!] });
      moved.add(o);
      moved.add(n);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (moved.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`, del: now === null ? p : undefined, put: now === null ? undefined : [p, now] });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const out: string[] = [];
  for (const r of rows) {
    out.push(r.line);
    if (check) continue;
    if (r.del !== undefined) rmSync(r.del, { force: true });
    if (r.put !== undefined) {
      mkdirSync(dirname(r.put[0]), { recursive: true });
      writeFileSync(r.put[0], r.put[1]);
    }
  }
  out.push(`ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`);
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
