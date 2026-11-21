import { mkdirSync as _K, readdirSync as _M, readFileSync as _N, writeFileSync as _P } from 'node:fs';
import { join } from 'node:path';
const _Q = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const _R = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DIRS: ReadonlyArray<readonly [number, number, string, string]> = [
[0, -1, 'u', 'U'],
[0, 1, 'd', 'D'],
[-1, 0, 'l', 'L'],
[1, 0, 'r', 'R'],
];
interface Level {
w: number;
h: number;
_e: Uint8Array;
_c: number[];
_b: number[];
_d: number;
}
function _A(text: string): Level {
const rows = text.split('\n').filter((r) => r.length > 0);
const h = rows.length;
const w = Math.max(...rows.map((r) => r.length));
const _e = new Uint8Array(w * h).fill(1);
const _c: number[] = [];
const _b: number[] = [];
let _d = -1;
rows.forEach((row, y) => {
for (let x = 0; x < row.length; x++) {
const ch = row[x]!;
const i = y * w + x;
if (ch === '#') continue;
_e[i] = 0;
if (ch === '.'|| ch === '*'|| ch === '+') _c.push(i);
if (ch === '$'|| ch === '*') _b.push(i);
if (ch === '@'|| ch === '+') _d = i;
}
});
for (let y = 0; y < h; y++) {
for (let x = 0; x < w; x++) {
if (x === 0 || y === 0 || x === w - 1 || y === h - 1) _e[y * w + x] = 1;
}
}
_b.sort((a, b) => a - b);
return { w, h, _e, _c, _b, _d };
}
function _B(_a: Level): Uint8Array {
const { w, _e, _c } = _a;
const _j = new Uint8Array(_e.length);
const queue = [..._c];
for (const g of _c) _j[g] = 1;
for (let qi = 0; qi < queue.length; qi++) {
const x = queue[qi]!;
for (const [dx, dy] of DIRS) {
const d = dy * w + dx;
const y = x - d;
if (_e[y] === 0 && _e[y - d] === 0 && !_j[y]) {
_j[y] = 1;
queue.push(y);
}
}
}
return _j;
}
function _C(_a: Level): Int32Array[] {
const { w, _e, _c } = _a;
const out: Int32Array[] = [];
for (const g of _c) {
const _i = new Int32Array(_e.length).fill(-1);
_i[g] = 0;
const queue = [g];
for (let qi = 0; qi < queue.length; qi++) {
const x = queue[qi]!;
for (const [dx, dy] of DIRS) {
const d = dy * w + dx;
const y = x - d;
if (_e[y] === 0 && _e[y - d] === 0 && _i[y] < 0) {
_i[y] = _i[x]! + 1;
queue.push(y);
}
}
}
out.push(_i);
}
return out;
}
function reach(
_a: Level,
_f: Uint8Array,
from: number,
seen: Int32Array,
stamp: number,
stack: Int32Array,
): number {
const { w, _e } = _a;
let low = from;
let n = 0;
stack[n++] = from;
seen[from] = stamp;
while (n > 0) {
const p = stack[--n]!;
if (p < low) low = p;
const q0 = p - w;
const q1 = p + w;
const q2 = p - 1;
const q3 = p + 1;
if (_e[q0] === 0 && _f[q0] === 0 && seen[q0] !== stamp) { seen[q0] = stamp; stack[n++] = q0; }
if (_e[q1] === 0 && _f[q1] === 0 && seen[q1] !== stamp) { seen[q1] = stamp; stack[n++] = q1; }
if (_e[q2] === 0 && _f[q2] === 0 && seen[q2] !== stamp) { seen[q2] = stamp; stack[n++] = q2; }
if (_e[q3] === 0 && _f[q3] === 0 && seen[q3] !== stamp) { seen[q3] = stamp; stack[n++] = q3; }
}
return low;
}
function _D(_a: Level, _f: Uint8Array, _k: Uint8Array, t: number): boolean {
const { w, _e } = _a;
for (const a of [t, t - 1, t - w, t - w - 1]) {
const b = a + 1;
const c = a + w;
const d = c + 1;
if (!(_e[a] || _f[a]) || !(_e[b] || _f[b]) || !(_e[c] || _f[c]) || !(_e[d] || _f[d])) continue;
if ((_f[a] && !_k[a]) || (_f[b] && !_k[b]) || (_f[c] && !_k[c]) || (_f[d] && !_k[d])) return true;
}
return false;
}
function _E(_b: number[], low: number, size: number): number {
let k = low;
for (const b of _b) k = k * size + b;
return k;
}
function _F(_a: Level, _f: Uint8Array, from: number, to: number): string {
const { w, _e } = _a;
if (from === to) return '';
const prev = new Int32Array(_e.length).fill(-1);
const how = new Array<string>(_e.length);
const queue = [from];
prev[from] = from;
for (let qi = 0; qi < queue.length; qi++) {
const p = queue[qi]!;
if (p === to) break;
for (const [dx, dy, letter] of DIRS) {
const q = p + dy * w + dx;
if (_e[q] || _f[q] || prev[q] !== -1) continue;
prev[q] = p;
how[q] = letter;
queue.push(q);
}
}
if (prev[to] === -1) throw new Error('walkTo: push square out of reach');
let s = '';
for (let p = to; p !== from; p = prev[p]!) s = how[p]! + s;
return s;
}
function _G(w: number, from: number, _m: string): number {
let p = from;
for (const ch of _m.toLowerCase()) p += ch === 'u'? -w : ch === 'd'? w : ch === 'l'? -1 : 1;
return p;
}
interface PushSolution {
pushes: number;
_m: string;
}
function _H(_a: Level, maxStates: number, weight: number): PushSolution | null {
const { w, _e, _c } = _a;
const size = _e.length;
const _k = new Uint8Array(size);
for (const g of _c) _k[g] = 1;
const _j = _B(_a);
if (_a._b.some((b) => !_j[b])) return null;
const _i = _C(_a);
const n = _a._b.length;
const _h = (bs: number[]): boolean => bs.every((b) => _k[b]);
const _g = (bs: number[]): number => {
let best = Infinity;
const perm = _c.map((_, i) => i);
const rec = (k: number, acc: number): void => {
if (acc >= best) return;
if (k === n) {
best = acc;
return;
}
for (let i = k; i < n; i++) {
[perm[k], perm[i]] = [perm[i]!, perm[k]!];
const d = _i[perm[k]!]![bs[k]!]!;
if (d >= 0) rec(k + 1, acc + d);
[perm[k], perm[i]] = [perm[i]!, perm[k]!];
}
};
rec(0, 0);
return best === Infinity ? 1e9 : best;
};
const _f = new Uint8Array(size);
const seen = new Int32Array(size);
const mark = new Int32Array(size);
const stack = new Int32Array(size);
let stamp = 0;
const sBoxes: number[][] = [_a._b.slice()];
const sPlayer: number[] = [_a._d];
const sG: number[] = [0];
const sParent: number[] = [-1];
const sFrom: number[] = [-1];
const sTo: number[] = [-1];
const sF: number[] = [weight * _g(_a._b)];
const sSeq: number[] = [0];
const heap: number[] = [0];
const less = (a: number, b: number): boolean =>
sF[a]! !== sF[b]!
? sF[a]! < sF[b]!
: sG[a]! !== sG[b]!
? sG[a]! > sG[b]!
: sSeq[a]! < sSeq[b]!;
const heapPush = (t: number): void => {
let i = heap.length;
heap.push(t);
while (i > 0) {
const p = (i - 1) >> 1;
if (!less(heap[i]!, heap[p]!)) break;
[heap[i], heap[p]] = [heap[p]!, heap[i]!];
i = p;
}
};
const heapPop = (): number => {
const top = heap[0]!;
const last = heap.pop()!;
if (heap.length > 0) {
heap[0] = last;
for (let i = 0; ; ) {
let c = 2 * i + 1;
if (c >= heap.length) break;
if (c + 1 < heap.length && less(heap[c + 1]!, heap[c]!)) c++;
if (!less(heap[c]!, heap[i]!)) break;
[heap[i], heap[c]] = [heap[c]!, heap[i]!];
i = c;
}
}
return top;
};
const bestG = new Map<number, number>();
const hCache = new Map<number, number>();
const hOf = (bs: number[]): number => {
const k = _E(bs, 0, size);
let h = hCache.get(k);
if (h === undefined) {
h = _g(bs);
hCache.set(k, h);
}
return h;
};
for (const b of _a._b) _f[b] = 1;
const low0 = reach(_a, _f, _a._d, seen, ++stamp, stack);
for (const b of _a._b) _f[b] = 0;
bestG.set(_E(_a._b, low0, size), 0);
if (_h(_a._b)) return { pushes: 0, _m: ''};
let found = -1;
while (heap.length > 0 && found < 0) {
const s = heapPop();
const _b = sBoxes[s]!;
for (const b of _b) _f[b] = 1;
const low = reach(_a, _f, sPlayer[s]!, seen, ++stamp, stack);
if (bestG.get(_E(_b, low, size)) !== sG[s]) {
for (const b of _b) _f[b] = 0;
continue;
}
const here = stamp;
for (let bi = 0; bi < _b.length && found < 0; bi++) {
const b = _b[bi]!;
for (const [dx, dy] of DIRS) {
const d = dy * w + dx;
const t = b + d;
if (seen[b - d] !== here || _e[t] || _f[t] || !_j[t]) continue;
_f[b] = 0;
_f[t] = 1;
const frozen = _D(_a, _f, _k, t);
let next: number[] | null = null;
let k = -1;
if (!frozen) {
next = _b.slice();
next[bi] = t;
next.sort((a, c) => a - c);
k = _E(next, reach(_a, _f, b, mark, ++stamp, stack), size);
}
_f[t] = 0;
_f[b] = 1;
if (frozen || next === null) continue;
const g = sG[s]! + 1;
const prev = bestG.get(k);
if (prev !== undefined && prev <= g) continue;
if (sBoxes.length >= maxStates) {
for (const x of _b) _f[x] = 0;
return null;
}
bestG.set(k, g);
const h = hOf(next);
const tIdx = sBoxes.length;
sBoxes.push(next);
sPlayer.push(b);
sG.push(g);
sParent.push(s);
sFrom.push(b);
sTo.push(t);
sF.push(g + weight * h);
sSeq.push(tIdx);
heapPush(tIdx);
if (_h(next)) {
found = tIdx;
break;
}
}
}
for (const x of _b) _f[x] = 0;
}
if (found < 0) return null;
const path: number[] = [];
for (let s = found; s > 0; s = sParent[s]!) path.push(s);
path.reverse();
let _m = '';
let _d = _a._d;
let _b = _a._b;
for (const s of path) {
const nextBoxes = sBoxes[s]!;
const from = sFrom[s]!;
const to = sTo[s]!;
const d = to - from;
const dir = DIRS.find(([dx, dy]) => dy * w + dx === d)!;
for (const b of _b) _f[b] = 1;
_m += _F(_a, _f, _d, from - d);
for (const b of _b) _f[b] = 0;
_m += dir[3];
_d = from;
_b = nextBoxes;
}
return { pushes: path.length, _m };
}
interface Room {
_b: number[];
_c: number[];
}
function _I(_a: Level): Room[] | null {
const { w, _e, _c, _b, _d } = _a;
const _j = _B(_a);
const row = Math.floor(_d / w);
const cut = new Uint8Array(_e.length);
for (let i = row * w; i < (row + 1) * w; i++) if (!_e[i] && !_j[i]) cut[i] = 1;
if (_b.some((b) => cut[b])) return null;
const part = new Int32Array(_e.length).fill(-1);
const _l: Room[] = [];
for (let s = 0; s < _e.length; s++) {
if (_e[s] || cut[s] || part[s] >= 0) continue;
const squares = [s];
part[s] = _l.length;
for (let i = 0; i < squares.length; i++) {
for (const [dx, dy] of DIRS) {
const q = squares[i]! + dy * w + dx;
if (!_e[q] && !cut[q] && part[q] < 0) {
part[q] = _l.length;
squares.push(q);
}
}
}
_l.push({ _b: [], _c: [] });
}
for (const b of _b) _l[part[b]!]!._b.push(b);
for (const g of _c) if (part[g]! >= 0) _l[part[g]!]!._c.push(g);
if (_c.some((g) => part[g]! < 0) || _l.some((r) => r._b.length !== r._c.length)) return null;
return _l.filter((r) => r._b.length > 0);
}
function _J(text: string): string {
const _a = _A(text);
const _l = _I(_a);
if (_l !== null) {
let _d = _a._d;
let _m = '';
let ok = true;
const done: boolean[] = _l.map(() => false);
for (let ri = 0; ri < _l.length; ri++) {
const room = _l[ri]!;
const _e = _a._e.slice();
for (let oj = 0; oj < _l.length; oj++) {
if (oj === ri) continue;
const other = _l[oj]!;
for (const b of done[oj]! ? other._c : other._b) _e[b] = 1;
}
const sub: Level = {
w: _a.w,
h: _a.h,
_e,
_c: room._c.slice().sort((a, b) => a - b),
_b: room._b.slice().sort((a, b) => a - b),
_d,
};
const _h =
_H(sub, 400_000, 1) ??
_H(sub, 400_000, 4) ??
null;
if (_h === null) {
ok = false;
break;
}
_m += _h._m;
_d = _G(_a.w, _d, _h._m);
done[ri] = true;
}
if (ok) return _m;
}
return (
_H(_a, 400_000, 1)?._m ??
_H(_a, 400_000, 4)?._m ??
''
);
}
for (const id of _M(_Q).sort()) {
const _m = _J(_N(join(_Q, id, 'level.txt'), 'utf8'));
_K(join(_R, id), { recursive: true });
_P(join(_R, id, 'solution.txt'), `${_m}\n`);
}