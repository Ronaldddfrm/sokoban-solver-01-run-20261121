# Sokoban solver

Push-optimal Sokoban solver for make.fun's "Build the best Sokoban solver,
21 November 2026" bounty.

## How it works

A generated level is a hallway plus one to four rooms, and a box can never
leave its room (a box pushed into the hallway reaches no goal). So the
level's push-optimum is the sum of the rooms' optima, and each room is solved
on its own with the other rooms' boxes treated as walls.

Each room is solved with A* over pushes. A state is the boxes' squares plus
the player's reachable region (named by its lowest square). The estimate is
the cheapest assignment of boxes to goals under push-distances that ignore
the other boxes (a pull-BFS from each goal), which never overestimates, so
the first solved state A* pops is push-optimal for that room. Two deadlocks
are pruned: a box on a square from which no pull reaches any goal, and a
frozen 2x2 block of walls and boxes with a box off its goal.

The search is budgeted by work (states generated), never by the clock, so two
runs write the same bytes. If the optimal search gives up on a room, a
weighted search and then a plain move-based A* still try to solve it.

## Run

```sh
node main.ts   # reads /input/<id>/level.txt, writes /output/<id>/solution.txt
```

Local check against the kit's practice set:

```sh
MAKEFUN_INPUT_DIR=<kit>/practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

## Results (local, practice set)

Score **1,000,000** — every instance solved in exactly P\* pushes
(i001: 13, i002: 16, i003: 29, i004: 47, i005: 60), in under a second for the
whole set. The same score held on six further sets drawn from the published
generator with different seeds.
