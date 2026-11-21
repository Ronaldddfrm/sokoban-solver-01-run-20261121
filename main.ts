// Sokoban solver: push-optimal per room, then concatenated.
//
// Idea: a generated level is a hallway plus one to four rooms, and a box can
// never leave its room (a box pushed into the hallway reaches no goal). So the
// level's push-optimum is the sum of the rooms' optima, and each room is
// solved on its own with the other rooms' boxes treated as walls.
//
// Each room is solved with A* over pushes. A state is the boxes' squares plus
// the player's reachable region (named by its lowest square). The estimate is
// the cheapest assignment of boxes to goals under push-distances that ignore
// the other boxes (a pull-BFS from each goal), which never overestimates, so
// the first solved state A* pops is push-optimal for that room. Two deadlocks
// are pruned: a box on a square from which no pull reaches any goal, and a
// frozen 2x2 block of walls and boxes with a box off its goal. Neither prunes
// a solvable state.
//
// The search is budgeted by work (states generated), never by the clock, so
// two runs write the same bytes. If the optimal search gives up on a room,
// a weighted search and then a plain move-based A* still try to solve it,
// because a solved level at more than the optimum still earns points.
//
// Node 22 runs this file as it is (erasable TypeScript only, no imports
// beyond node:fs / node:path). Input /input/<id>/level.txt, output
// /output/<id>/solution.txt; MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR stand
// in for the mounts outside a container.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

/** [dx, dy, step letter, push letter] */
const DIRS: ReadonlyArray<readonly [number, number, string, string]> = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

/** Parse XSB text. Short rows and the outer frame count as walls. */
function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x]!;
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/**
 * Squares from which a box can be pulled back onto some goal, ignoring the
 * other boxes. A box anywhere else is dead: no push ever saves it.
 */
function liveSquares(level: Level): Uint8Array {
  const { w, wall, goals } = level;
  const live = new Uint8Array(wall.length);
  const queue = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi]!;
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const y = x - d;
      if (wall[y] === 0 && wall[y - d] === 0 && !live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

/**
 * Push-distances that ignore the other boxes: dist[g][s] is the fewest
 * pushes moving one box from s onto goal g (or -1 when unreachable). A pull
 * BFS from each goal, the reverse of a push.
 */
function pushDistances(level: Level): Int32Array[] {
  const { w, wall, goals } = level;
  const out: Int32Array[] = [];
  for (const g of goals) {
    const dist = new Int32Array(wall.length).fill(-1);
    dist[g] = 0;
    const queue = [g];
    for (let qi = 0; qi < queue.length; qi++) {
      const x = queue[qi]!;
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const y = x - d;
        if (wall[y] === 0 && wall[y - d] === 0 && dist[y] < 0) {
          dist[y] = dist[x]! + 1;
          queue.push(y);
        }
      }
    }
    out.push(dist);
  }
  return out;
}

/**
 * Flood-fill the squares the player reaches from `from` with `occupied` in
 * the way, marking them in `seen` with `stamp`; returns the lowest square.
 */
function reach(
  level: Level,
  occupied: Uint8Array,
  from: number,
  seen: Int32Array,
  stamp: number,
  stack: Int32Array,
): number {
  const { w, wall } = level;
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
    if (wall[q0] === 0 && occupied[q0] === 0 && seen[q0] !== stamp) { seen[q0] = stamp; stack[n++] = q0; }
    if (wall[q1] === 0 && occupied[q1] === 0 && seen[q1] !== stamp) { seen[q1] = stamp; stack[n++] = q1; }
    if (wall[q2] === 0 && occupied[q2] === 0 && seen[q2] !== stamp) { seen[q2] = stamp; stack[n++] = q2; }
    if (wall[q3] === 0 && occupied[q3] === 0 && seen[q3] !== stamp) { seen[q3] = stamp; stack[n++] = q3; }
  }
  return low;
}

/** Whether the box just pushed to `t` sits in a frozen 2x2 block. */
function frozenBlock(level: Level, occupied: Uint8Array, goal: Uint8Array, t: number): boolean {
  const { w, wall } = level;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1;
    const c = a + w;
    const d = c + 1;
    if (!(wall[a] || occupied[a]) || !(wall[b] || occupied[b]) || !(wall[c] || occupied[c]) || !(wall[d] || occupied[d])) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) || (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

/** A state's key: region low square, then the boxes, as digits in base size. */
function keyOf(boxes: number[], low: number, size: number): number {
  let k = low;
  for (const b of boxes) k = k * size + b;
  return k;
}

/** Shortest walk from `from` to `to` around walls and boxes, lower LURD. */
function walkTo(level: Level, occupied: Uint8Array, from: number, to: number): string {
  const { w, wall } = level;
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi]!;
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
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

/** The square the player stands on after `moves` from `from`. */
function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

interface PushSolution {
  pushes: number;
  moves: string;
}

/**
 * A* over pushes on one (sub-)level. `weight` 1 is optimal; a larger weight
 * searches greedily and may return a longer solution. Null when the budget
 * of generated states runs out or the level has no solution.
 */
function solvePushes(level: Level, maxStates: number, weight: number): PushSolution | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(level);
  if (level.boxes.some((b) => !live[b])) return null;
  const dist = pushDistances(level);
  const n = level.boxes.length;
  const solved = (bs: number[]): boolean => bs.every((b) => goal[b]);

  // Cheapest assignment of boxes to goals under the push-distances.
  // n <= 4 here, so all permutations are cheap; -1 (unreachable) means no
  // assignment through that pair.
  const estimate = (bs: number[]): number => {
    let best = Infinity;
    const perm = goals.map((_, i) => i);
    const rec = (k: number, acc: number): void => {
      if (acc >= best) return;
      if (k === n) {
        best = acc;
        return;
      }
      for (let i = k; i < n; i++) {
        [perm[k], perm[i]] = [perm[i]!, perm[k]!];
        const d = dist[perm[k]!]![bs[k]!]!;
        if (d >= 0) rec(k + 1, acc + d);
        [perm[k], perm[i]] = [perm[i]!, perm[k]!];
      }
    };
    rec(0, 0);
    return best === Infinity ? 1e9 : best;
  };

  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;

  // States, in order found: boxes, player square, pushes so far, parent, and
  // the push (from -> to) that made the state.
  const sBoxes: number[][] = [level.boxes.slice()];
  const sPlayer: number[] = [level.player];
  const sG: number[] = [0];
  const sParent: number[] = [-1];
  const sFrom: number[] = [-1];
  const sTo: number[] = [-1];
  const sF: number[] = [weight * estimate(level.boxes)];
  const sSeq: number[] = [0];

  // Open list: binary heap on (f, then higher g, then earlier sequence).
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
    const k = keyOf(bs, 0, size);
    let h = hCache.get(k);
    if (h === undefined) {
      h = estimate(bs);
      hCache.set(k, h);
    }
    return h;
  };

  for (const b of level.boxes) occupied[b] = 1;
  const low0 = reach(level, occupied, level.player, seen, ++stamp, stack);
  for (const b of level.boxes) occupied[b] = 0;
  bestG.set(keyOf(level.boxes, low0, size), 0);
  if (solved(level.boxes)) return { pushes: 0, moves: '' };

  let found = -1;
  while (heap.length > 0 && found < 0) {
    const s = heapPop();
    const boxes = sBoxes[s]!;
    // This state's region, stamped on `seen` as `here`; a stale heap entry
    // (a better path to the same key was found since) is skipped.
    for (const b of boxes) occupied[b] = 1;
    const low = reach(level, occupied, sPlayer[s]!, seen, ++stamp, stack);
    if (bestG.get(keyOf(boxes, low, size)) !== sG[s]) {
      for (const b of boxes) occupied[b] = 0;
      continue;
    }
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi]!;
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        if (seen[b - d] !== here || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(level, occupied, goal, t);
        let next: number[] | null = null;
        let k = -1;
        if (!frozen) {
          next = boxes.slice();
          next[bi] = t;
          next.sort((a, c) => a - c);
          k = keyOf(next, reach(level, occupied, b, mark, ++stamp, stack), size);
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || next === null) continue;
        const g = sG[s]! + 1;
        const prev = bestG.get(k);
        if (prev !== undefined && prev <= g) continue;
        if (sBoxes.length >= maxStates) {
          for (const x of boxes) occupied[x] = 0;
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
        if (solved(next)) {
          found = tIdx;
          break;
        }
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;

  const path: number[] = [];
  for (let s = found; s > 0; s = sParent[s]!) path.push(s);
  path.reverse();
  let moves = '';
  let player = level.player;
  let boxes = level.boxes;
  for (const s of path) {
    const nextBoxes = sBoxes[s]!;
    const from = sFrom[s]!;
    const to = sTo[s]!;
    const d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d)!;
    for (const b of boxes) occupied[b] = 1;
    moves += walkTo(level, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    moves += dir[3];
    player = from;
    boxes = nextBoxes;
  }
  return { pushes: path.length, moves };
}

/**
 * Plain A* over single steps (player moves), the fallback when no push
 * search solves a level: it still solves, just not in the fewest pushes.
 */
function solveMoves(level: Level, maxStates: number): string {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const dist = pushDistances(level);
  const est = (bs: number[]): number => {
    let sum = 0;
    for (const b of bs) {
      let m = Infinity;
      for (let gi = 0; gi < goals.length; gi++) {
        const d = dist[gi]![b]!;
        if (d >= 0 && d < m) m = d;
      }
      sum += m === Infinity ? 1000 : m;
    }
    return sum;
  };
  const key = (p: number, bs: number[]): string => `${p}|${bs.join(',')}`;
  const sp: number[] = [level.player];
  const sb: number[][] = [level.boxes.slice()];
  const sg: number[] = [0];
  const parent: number[] = [-1];
  const step: string[] = [''];
  const best = new Map<string, number>([[key(level.player, level.boxes), 0]]);
  const heap: number[] = [0];
  const fOf = (t: number): number => sg[t]! + est(sb[t]!);
  const less = (a: number, b: number): boolean => fOf(a) !== fOf(b) ? fOf(a) < fOf(b) : a < b;
  const push = (t: number): void => {
    let i = heap.length;
    heap.push(t);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i]!, heap[p]!)) break;
      [heap[i], heap[p]] = [heap[p]!, heap[i]!];
      i = p;
    }
  };
  const pop = (): number => {
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
  let expanded = 0;
  while (heap.length > 0 && expanded < maxStates) {
    const s = pop();
    if (best.get(key(sp[s]!, sb[s]!)) !== sg[s]) continue;
    const bs = sb[s]!;
    if (bs.every((b) => goal[b])) {
      let moves = '';
      for (let t = s; t > 0; t = parent[t]!) moves = step[t]! + moves;
      return moves;
    }
    expanded++;
    const p = sp[s]!;
    for (const [dx, dy, letter] of DIRS) {
      const d = dy * w + dx;
      const q = p + d;
      if (wall[q]) continue;
      let nb = bs;
      let move = letter;
      const at = bs.indexOf(q);
      if (at >= 0) {
        if (wall[q + d] || bs.includes(q + d)) continue;
        nb = bs.slice();
        nb[at] = q + d;
        nb.sort((a, b) => a - b);
        move = letter.toUpperCase();
      }
      const k = key(q, nb);
      const seenG = best.get(k);
      if (seenG !== undefined && seenG <= sg[s]! + 1) continue;
      const t = sp.length;
      sp.push(q);
      sb.push(nb);
      sg.push(sg[s]! + 1);
      parent.push(s);
      step.push(move);
      best.set(k, sg[s]! + 1);
      push(t);
    }
  }
  return '';
}

interface Room {
  boxes: number[];
  goals: number[];
}

/**
 * The level's rooms: cut the dead squares of the player's row (the hallway:
 * a box there reaches no goal) out of the floor; each part left that holds a
 * box is a room. Null when the level is no set of rooms.
 */
function roomsOf(level: Level): Room[] | null {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(level);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: Room[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i]! + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ boxes: [], goals: [] });
  }
  for (const b of boxes) rooms[part[b]!]!.boxes.push(b);
  for (const g of goals) if (part[g]! >= 0) rooms[part[g]!]!.goals.push(g);
  if (goals.some((g) => part[g]! < 0) || rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/** Solve one level: room by room, optimal pushes each, concatenated. */
function solve(text: string): string {
  const level = parseLevel(text);
  const rooms = roomsOf(level);
  if (rooms !== null) {
    let player = level.player;
    let moves = '';
    let ok = true;
    const done: boolean[] = rooms.map(() => false);
    for (let ri = 0; ri < rooms.length; ri++) {
      const room = rooms[ri]!;
      const wall = level.wall.slice();
      for (let oj = 0; oj < rooms.length; oj++) {
        if (oj === ri) continue;
        const other = rooms[oj]!;
        for (const b of done[oj]! ? other.goals : other.boxes) wall[b] = 1;
      }
      const sub: Level = {
        w: level.w,
        h: level.h,
        wall,
        goals: room.goals.slice().sort((a, b) => a - b),
        boxes: room.boxes.slice().sort((a, b) => a - b),
        player,
      };
      const solved =
        solvePushes(sub, 400_000, 1) ??
        solvePushes(sub, 400_000, 4) ??
        null;
      if (solved === null) {
        ok = false;
        break;
      }
      moves += solved.moves;
      player = endOf(level.w, player, solved.moves);
      done[ri] = true;
    }
    if (ok) return moves;
  }
  // Fallback: the whole level at once, then a plain move search.
  return (
    solvePushes(level, 400_000, 1)?.moves ??
    solvePushes(level, 400_000, 4)?.moves ??
    solveMoves(level, 200_000)
  );
}

for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
