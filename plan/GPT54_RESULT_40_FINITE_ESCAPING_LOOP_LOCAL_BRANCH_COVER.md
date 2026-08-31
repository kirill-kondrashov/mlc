# RESULT 40 — Finite local-branch cover of an escaping basin loop

## Summary

Landed corrected **Stage 2C** in a new leaf module:

- `Mlc/BottcherFiniteEscapingLoopCover.lean`

and registered it in `Mlc.lean` immediately after:

- `import Mlc.BottcherArbitraryFiniteLevelLift`

The new file adds:

- `BasinLoopFiniteLocalRootBranchCover`
- `BasinLoopFiniteLocalRootBranchCover.of_level_escapes`

This uses compactness of the time interval `Icc (0,1)` to extract a **finite
cover** of a uniformly level-`N` escaping basin loop by neighborhoods carrying
Stage-1 local holomorphic root branches.

## What is now proved

For every continuous basin loop `γ` whose whole image satisfies the level-`N`
outside-open escape condition, there is a finite family of times and associated
local branch neighborhoods such that every point of the loop lies in one of
those neighborhoods.

## What is **not** proved

This does **not** prove any of the following:

- equality of neighboring local branches;
- overlap compatibility or overlap multipliers;
- loop monodromy triviality;
- existence of a coherent global basin value;
- `holo_on_basin`.

All of those remain open.

## Validation

Ran successfully:

- `lake build`
- `lake env lean check_axioms.lean`

Both passed with exit code `0`.

## Honest remaining seam

After Result 40, the genuine Böttcher route has:

- unconditional basin preconnectedness;
- Stage 1 local root branches;
- Stage 2A one-step finite-level coherence;
- Stage 2B arbitrary finite-level lifting;
- Stage 2C finite local-branch covers for uniformly escaping loops.

Still missing are the genuinely global steps:

- compare branches on overlaps / along loops,
- control overlap multipliers,
- construct a single coherent basin value,
- discharge `holo_on_basin`.
