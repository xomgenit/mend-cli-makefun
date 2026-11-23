// mend: one patch tool for every AI edit format.
//
// Applies a patch in one of four formats (unified diff, SEARCH/REPLACE
// blocks, V4A, JSON edits) to the tree of text files rooted at the working
// directory. Every change is written, or none is: a failed edit is reported
// and the other edits still run, but no file is written at all when any edit
// failed. SPEC.md is the whole contract; this file implements it.
//
// Node 22, standard library alone. Run as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and then this file hands over to runner.ts (the last lines below): that
// hand-over and runner.ts stay exactly as the kit has them.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** A whole-run failure: exit 2 with exactly one line. */
class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One edit failed: reported, and the edit changes nothing. */
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A path is safe when it is not empty, does not start with /, holds no \, and none of its segments is empty, . or .. */
function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** Byte order of UTF-8 paths, for the output rows. */
function byteCmp(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

/** A file as lines: its own line break, its lines, and whether it ends with a break. */
interface FileLines {
  lines: string[];
  br: string;
  ends: boolean;
}

function splitFile(text: string): FileLines {
  if (text === '') return { lines: [], br: '\n', ends: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const ends = text.endsWith(br);
  if (ends) parts.pop();
  return { lines: parts, br, ends };
}

function joinFile(f: FileLines): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.ends ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
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
  set(p: string, v: string | null): void {
    this.now.set(p, v);
  }
}

type Edit = (tree: Tree) => void;

/** Remove leading/trailing spaces and tabs from a line, per tier. */
function normLine(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** Positions where O occurs in the file's lines at one tier (occurrences may overlap). */
function occurrencesAt(file: string[], old: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (old.length === 0 || old.length > file.length) return out;
  const want = old.map((l) => normLine(l, tier));
  for (let i = Math.max(0, from); i + old.length <= file.length; i += 1) {
    let ok = true;
    for (let j = 0; j < old.length; j += 1) {
      if (normLine(file[i + j]!, tier) !== want[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs at least once at or after `from`, with its positions. */
function findTier(file: string[], old: string[], strict: boolean, from: number): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const occ = occurrencesAt(file, old, tier, from);
    if (occ.length > 0) return { tier, occ };
  }
  return null;
}

/**
 * Re-indent an added line at tier 2: F is the leading spaces/tabs of the
 * file's first matched line, P those of O's first line; a non-empty,
 * non-whitespace line starting with P has that P replaced by F.
 */
function reindent(line: string, fileFirst: string, oldFirst: string): string {
  const f = /^[ \t]*/.exec(fileFirst)?.[0] ?? '';
  const p = /^[ \t]*/.exec(oldFirst)?.[0] ?? '';
  if (line === '' || line.trim() === '') return line;
  if (!line.startsWith(p)) return line;
  return f + line.slice(p.length);
}

/**
 * Build the lines that replace a matched block. `body` is the hunk/chunk
 * body in order: {kind, text} with kind 'ctx' (context), 'del', 'add'.
 * Context lines are written as the file's own matched lines; added lines
 * are re-indented at tier 2. `pos` is where O matched in the file.
 */
function buildReplacement(
  body: { kind: 'ctx' | 'del' | 'add'; text: string }[],
  file: string[],
  pos: number,
  tier: number,
  old: string[],
): string[] {
  const out: string[] = [];
  let oi = 0;
  for (const b of body) {
    if (b.kind === 'ctx') {
      out.push(file[pos + oi]!);
      oi += 1;
    } else if (b.kind === 'del') {
      oi += 1;
    } else {
      out.push(tier === 2 ? reindent(b.text, file[pos]!, old[0]!) : b.text);
    }
  }
  return out;
}

/** The `\` line after a hunk's last context or `+` line means no final line break. */
function hunkNoEol(body: { kind: 'ctx' | 'del' | 'add' | 'bs'; text: string }[]): boolean {
  for (let i = body.length - 1; i >= 0; i -= 1) {
    const b = body[i]!;
    if (b.kind === 'ctx' || b.kind === 'add') return body[i + 1]?.kind === 'bs';
    if (b.kind === 'bs') continue;
    return false;
  }
  return false;
}

/** Apply one hunk/chunk body to a file's lines. Returns the new lines and final-break flag. */
function applyBody(
  body: { kind: 'ctx' | 'del' | 'add' | 'bs'; text: string }[],
  f: FileLines,
  at: number,
  strict: boolean,
  kind: 'hunk' | 'chunk',
  cursor: number,
  eof: boolean,
): { lines: string[]; ends: boolean; cursor: number } {
  const old: string[] = [];
  const kept: { kind: 'ctx' | 'del' | 'add'; text: string }[] = [];
  for (const b of body) {
    if (b.kind === 'ctx' || b.kind === 'del') old.push(b.text);
    if (b.kind !== 'bs') kept.push({ kind: b.kind as 'ctx' | 'del' | 'add', text: b.text });
  }
  const lines = f.lines.slice();
  let ends = f.ends;
  const noEol = hunkNoEol(body);
  if (old.length === 0) {
    // An empty O inserts after the first A + d lines for a hunk (so index at + 1),
    // at the cursor for a chunk, or at the end of the file for an end-of-file chunk.
    const insertBase = kind === 'chunk' ? (eof ? lines.length : cursor) : at + 1;
    const atIndex = Math.min(insertBase, lines.length);
    const added = buildReplacement(kept, lines, atIndex, 0, ['']);
    lines.splice(atIndex, 0, ...added);
    // Section 6's end-of-file rule is for unified hunks only; a chunk keeps the file's final break.
    if (kind === 'hunk' && atIndex === lines.length) ends = !noEol;
    return { lines, ends, cursor: atIndex + added.length };
  }
  // Find the first tier with an occurrence at or after the cursor.
  const found = findTier(lines, old, strict, kind === 'chunk' ? cursor : 0);
  if (found === null) return { lines, ends, cursor: -1 };
  let occ = found.occ;
  if (eof) occ = occ.filter((p) => p + old.length === lines.length);
  if (occ.length === 0) return { lines, ends, cursor: -1 };
  // A hunk takes the occurrence nearest to `at`; a chunk takes the first at or after the cursor.
  let pos: number;
  if (kind === 'hunk') {
    pos = occ[0]!;
    for (const p of occ) {
      if (Math.abs(p - at) < Math.abs(pos - at)) pos = p;
    }
  } else {
    pos = occ[0]!;
  }
  const replacement = buildReplacement(kept, lines, pos, found.tier, old);
  const touchesEnd = pos + old.length === lines.length;
  lines.splice(pos, old.length, ...replacement);
  // Section 6's end-of-file rule is for unified hunks only; a chunk keeps the file's final break.
  if (kind === 'hunk' && touchesEnd) ends = !noEol;
  return { lines, ends, cursor: pos + replacement.length };
}

/** Format detection (SPEC.md section 4): the first rule that holds. */
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
      tree.set(p, text);
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
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const f = splitFile(before);
      if (line < 0 || line > f.lines.length) throw new Fail('no-match', p);
      f.lines.splice(line, 0, ...add);
      tree.set(p, joinFile(f));
    };
  }
  return null;
}

/** Read a JSON patch: one array, or one edit object per line. */
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

/** A unified hunk: its old start line and its body lines. */
interface Hunk {
  a: number;
  body: { kind: 'ctx' | 'del' | 'add' | 'bs'; text: string }[];
}

/** One unified section: one edit. `oldPath`/`newPath` null means /dev/null. */
interface Section {
  oldPath: string | null;
  newPath: string | null;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

/** The path after `--- `/`+++ `: up to the first tab, surrounding spaces removed, a/ or b/ stripped. */
function diffPath(rest: string): string {
  let p = rest.split('\t')[0]!.trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

const HUNK_HEAD = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;

/** Parse a unified patch into its sections (SPEC.md section 6). */
function unifiedEdits(lines: string[], strict: boolean, moves: [string, string][]): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let hunk: Hunk | null = null;
  let inHeader = false;
  let havePair = false;
  const closeHunk = (): void => {
    if (hunk !== null) {
      // Empty lines at the end of a body are not part of it.
      while (hunk.body.length > 0 && hunk.body[hunk.body.length - 1]!.kind === 'ctx' && hunk.body[hunk.body.length - 1]!.text === '') hunk.body.pop();
      cur!.hunks.push(hunk);
      hunk = null;
    }
  };
  const startSection = (oldP: string | null, newP: string | null): void => {
    closeHunk();
    cur = { oldPath: oldP, newPath: newP, create: false, del: false, hunks: [] };
    sections.push(cur);
    inHeader = true;
    havePair = false;
  };
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      startSection(m[1]!, m[2]!);
      i += 1;
      continue;
    }
    if (hunk !== null) {
      // The body ends at a `diff --git ` line or at a `--- ` line followed by a `+++ ` line;
      // a `--- ` line starts with `-`, so check that before treating a line as a body line.
      const endsBody = line.startsWith('diff --git ') || (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ '));
      if (!endsBody && (line === '' || line.startsWith(' ') || line.startsWith('-') || line.startsWith('+') || line.startsWith('\\'))) {
        if (line === '') hunk.body.push({ kind: 'ctx', text: '' });
        else if (line.startsWith(' ')) hunk.body.push({ kind: 'ctx', text: line.slice(1) });
        else if (line.startsWith('-')) hunk.body.push({ kind: 'del', text: line.slice(1) });
        else if (line.startsWith('+')) hunk.body.push({ kind: 'add', text: line.slice(1) });
        else hunk.body.push({ kind: 'bs', text: line.slice(1) });
        i += 1;
        continue;
      }
      // The body ends here; fall through to handle this line outside a body.
      closeHunk();
      inHeader = false;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_HEAD.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      hunk = { a: Number(m[1]), body: [] };
      inHeader = false;
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader && !havePair) {
        cur.oldPath = line.slice(4) === '/dev/null' ? null : diffPath(line.slice(4));
        cur.newPath = lines[i + 1]!.slice(4) === '/dev/null' ? null : diffPath(lines[i + 1]!.slice(4));
        havePair = true;
        i += 2;
        continue;
      }
      startSection(line.slice(4) === '/dev/null' ? null : diffPath(line.slice(4)), lines[i + 1]!.slice(4) === '/dev/null' ? null : diffPath(lines[i + 1]!.slice(4)));
      havePair = true;
      i += 2;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('rename from ')) cur.oldPath = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.newPath = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.create = true;
      else if (line.startsWith('deleted file mode')) cur.del = true;
      // index, old/new mode, similarity, dissimilarity, Index: and anything else: ignored.
      i += 1;
      continue;
    }
    // Outside bodies, lines that are not part of a section header are ignored (prose, code fences).
    i += 1;
  }
  closeHunk();
  return sections.map((sec) => unifiedEdit(sec, strict, moves));
}

/** One unified section as an edit. */
function unifiedEdit(sec: Section, strict: boolean, moves: [string, string][]): Edit {
  return (tree) => {
    const isCreate = sec.oldPath === null || sec.create;
    const isDelete = sec.newPath === null || sec.del;
    if (isCreate) {
      const p = sec.newPath!;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      const made: string[] = [];
      for (const h of sec.hunks) for (const b of h.body) if (b.kind === 'add') made.push(b.text);
      // A created file ends with a line break unless a \ line follows its last + line.
      let ends = true;
      for (let hi = sec.hunks.length - 1; hi >= 0; hi -= 1) {
        const h = sec.hunks[hi]!;
        let lastAdd = -1;
        h.body.forEach((b, bi) => {
          if (b.kind === 'add') lastAdd = bi;
        });
        if (lastAdd >= 0) {
          ends = h.body[lastAdd + 1]?.kind !== 'bs';
          break;
        }
      }
      tree.set(p, made.length === 0 ? '' : made.join('\n') + (ends ? '\n' : ''));
      return;
    }
    if (isDelete) {
      const p = sec.oldPath!;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.set(p, null);
      return;
    }
    const oldP = sec.oldPath!;
    const newP = sec.newPath!;
    const isMove = oldP !== newP;
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    if (isMove && !safe(newP)) throw new Fail('unsafe', newP);
    const before = tree.get(oldP);
    if (before === null) throw new Fail('missing', oldP);
    if (isMove && tree.get(newP) !== null) throw new Fail('exists', newP);
    let f = splitFile(before);
    let d = 0;
    for (const h of sec.hunks) {
      const r = applyBody(h.body, f, h.a - 1 + d, strict, 'hunk', 0, false);
      if (r.cursor === -1) throw new Fail('no-match', oldP);
      const oldLen = h.body.filter((b) => b.kind === 'ctx' || b.kind === 'del').length;
      const newLen = h.body.filter((b) => b.kind === 'ctx' || b.kind === 'add').length;
      d += newLen - oldLen;
      f = { lines: r.lines, br: f.br, ends: r.ends };
    }
    const out = joinFile(f);
    if (isMove) {
      tree.set(oldP, null);
      tree.set(newP, out);
      moves.push([oldP, newP]);
    } else {
      tree.set(oldP, out);
    }
  };
}

/** Parse SEARCH/REPLACE blocks (SPEC.md section 7). */
function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i + 1;
    // The path is the nearest line before SEARCH, after the previous block, that is not blank
    // and does not start with three backticks (surrounding whitespace removed).
    let path: string | null = null;
    for (let j = i - 1; j >= prevEnd; j -= 1) {
      const t = lines[j]!.trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${searchLine}`);
    // Find ======= then >>>>>>> REPLACE after the SEARCH line.
    let eq = -1;
    let rep = -1;
    for (let j = i + 1; j < lines.length; j += 1) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '>>>>>>> REPLACE') break;
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine}`);
    for (let j = eq + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine}`);
    const oldLines = lines.slice(i + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

/** One SEARCH/REPLACE block as an edit. */
function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    const f = splitFile(before);
    const found = findTier(f.lines, oldLines, strict, 0);
    if (found === null) throw new Fail('no-match', path);
    if (found.occ.length > 1) throw new Fail('ambiguous', path);
    const pos = found.occ[0]!;
    const replacement = oldLines.length === 0 ? [] : newLines.map((l) => (found.tier === 2 ? reindent(l, f.lines[pos]!, oldLines[0]!) : l));
    f.lines.splice(pos, oldLines.length, ...replacement);
    tree.set(path, joinFile(f));
  };
}

/** A V4A chunk: its anchor (null: none), body lines, and whether *** End of File ended it. */
interface VChunk {
  anchor: string | null;
  body: { kind: 'ctx' | 'del' | 'add' | 'bs'; text: string }[];
  eof: boolean;
}

/** Parse a V4A patch (SPEC.md section 8). */
function v4aEdits(lines: string[], strict: boolean, moves: [string, string][]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  const last = lines.map((l, i) => (blank(l) ? -1 : i)).filter((i) => i >= 0).pop()!;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i += 1;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      // A `+` line (even with empty rest) is a real line of the file; a truly blank line is not.
      // Blank lines at the end of a section are not part of it, so only those are stripped.
      const made: { text: string; plus: boolean }[] = [];
      i += 1;
      while (i < last) {
        const l = lines[i]!;
        if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ') || l.trim() === '*** End Patch') break;
        if (blank(l)) {
          made.push({ text: '', plus: false });
          i += 1;
          continue;
        }
        if (!l.startsWith('+')) throw new Exit2(`error: parse ${i + 1}`);
        made.push({ text: l.slice(1), plus: true });
        i += 1;
      }
      while (made.length > 0 && !made[made.length - 1]!.plus) made.pop();
      const content = made.length === 0 ? '' : made.map((m) => m.text).join('\n') + '\n';
      edits.push(((p, c) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.set(p, c);
      })(path, content));
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      edits.push(((p) => (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.set(p, null);
      })(path));
      i += 1;
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const updateLine = i + 1;
      i += 1;
      let moveTo: string | null = null;
      const chunks: VChunk[] = [];
      let chunk: VChunk | null = null;
      const closeChunk = (): void => {
        if (chunk !== null) {
          chunks.push(chunk);
          chunk = null;
        }
      };
      while (i < last) {
        const l = lines[i]!;
        if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ') || l.trim() === '*** End Patch') break;
        if (blank(l)) {
          if (chunk !== null) chunk.body.push({ kind: 'ctx', text: '' });
          i += 1;
          continue;
        }
        if (l.startsWith('*** Move to: ') && chunk === null && chunks.length === 0 && moveTo === null) {
          moveTo = l.slice('*** Move to: '.length).trim();
          i += 1;
          continue;
        }
        if (l.trim() === '*** End of File') {
          if (chunk === null) throw new Exit2(`error: parse ${i + 1}`);
          chunk.eof = true;
          closeChunk();
          i += 1;
          continue;
        }
        if (l.startsWith('@@')) {
          closeChunk();
          chunk = { anchor: l.slice(2).trim() === '' ? null : l.slice(2).trim(), body: [], eof: false };
          i += 1;
          continue;
        }
        if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
          if (chunk === null) chunk = { anchor: null, body: [], eof: false };
          if (l.startsWith(' ')) chunk.body.push({ kind: 'ctx', text: l.slice(1) });
          else if (l.startsWith('-')) chunk.body.push({ kind: 'del', text: l.slice(1) });
          else chunk.body.push({ kind: 'add', text: l.slice(1) });
          i += 1;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      closeChunk();
      // Blank lines at the end of a section are not part of it: drop trailing empty context lines.
      if (chunks.length > 0) {
        const lastChunk = chunks[chunks.length - 1]!;
        if (!lastChunk.eof) while (lastChunk.body.length > 0 && lastChunk.body[lastChunk.body.length - 1]!.kind === 'ctx' && lastChunk.body[lastChunk.body.length - 1]!.text === '') lastChunk.body.pop();
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLine}`);
      edits.push(v4aUpdateEdit(path, moveTo, chunks, strict, moves));
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  return edits;
}

/** One V4A Update File section as an edit. */
function v4aUpdateEdit(path: string, moveTo: string | null, chunks: VChunk[], strict: boolean, moves: [string, string][]): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const before = tree.get(path);
    if (before === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    let f = splitFile(before);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null) {
        // Find the first line at or after the cursor equal to the anchor, at the first tier with one.
        const tiers = strict ? [0] : [0, 1, 2];
        let foundAt = -1;
        for (const tier of tiers) {
          const want = normLine(ch.anchor, tier);
          for (let k = cursor; k < f.lines.length; k += 1) {
            if (normLine(f.lines[k]!, tier) === want) {
              foundAt = k;
              break;
            }
          }
          if (foundAt >= 0) break;
        }
        if (foundAt < 0) throw new Fail('no-match', path);
        cursor = foundAt + 1;
      }
      const r = applyBody(ch.body, f, 0, strict, 'chunk', cursor, ch.eof);
      if (r.cursor === -1) throw new Fail('no-match', path);
      cursor = r.cursor;
      f = { lines: r.lines, br: f.br, ends: r.ends };
    }
    const out = joinFile(f);
    if (moveTo !== null) {
      tree.set(path, null);
      tree.set(moveTo, out);
      moves.push([path, moveTo]);
    } else {
      tree.set(path, out);
    }
  };
}

/** Run the CLI on argv; returns the exit code and the stdout lines. */
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
  const moves: [string, string][] = [];
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict, moves);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict, moves);
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
      // A failed edit changes nothing; the edits after it still run.
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }
  // Output rows: one per path whose state changed, in byte order of the paths.
  // A move that succeeded replaces its D and A lines with one R line, sorted by its new path.
  const rows: { key: string; text: string }[] = [];
  const replaced = new Set<string>();
  for (const [oldP, newP] of moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      replaced.add(oldP);
      replaced.add(newP);
    }
  }
  for (const p of [...tree.now.keys()].sort(byteCmp)) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (!replaced.has(p)) rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  rows.sort((a, b) => byteCmp(a.key, b.key));
  const out = rows.map((r) => r.text);
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
