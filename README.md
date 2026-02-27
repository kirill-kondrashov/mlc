# MLC Formalization Status

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph (rooted at `MLC.mlc_conjecture`)](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository is a Lean formalization scaffold centered on `MLC.mlc_conjecture`.
The code compiles and `MLC.mlc_conjecture` is `sorry`-free.

## Current Axiom Frontier (`make check`)

As of 2026-02-27, exactly one non-core axiom remains in the root theorem:

- `MLC.greenRayLogGtAnchorTwo_axiom_seed`

This axiom is **not** in the allowed frontier. The allowed frontier
remains core-only:

- `Quot.sound`
- `propext`
- `Classical.choice`

So `make check` currently fails with an axiom-frontier violation until this
axiom is eliminated. Eliminating it is the immediate next milestone.

Expected output:

```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.greenRayLogGtAnchorTwo_axiom_seed
```

## Progress Snapshot (Effort In Hours, Not Weeks)

| Target Axiom | Progress | Left | Estimated Remaining Effort |
|---|---|---|---|
| `greenRayLogGtAnchorTwo_axiom_seed` | `█████████░` 86% | 14% | ~90-240 Lean LOC, ~3-9 hrs |

Total estimated remainder: ~90-240 Lean LOC, ~3-9 hours.

## Active Plans (`plan/*`)

| File | Relevance | Progress | Left | Estimated Remaining Effort |
|---|---|---|---|---|
| `plan/PLAN_axiom_elimination_status.md` | ⭐⭐⭐⭐⭐ | `██████████` 100% | 0% | latest cycle summary |

## Key Technical Reality

- The old global anchor-gap seam is inconsistent in the current model:
  `not_greenRayLogGtAnchorTwoSeam`.
- The bounded-cutoff replacement route is also inconsistent:
  `not_greenRayLogGtAnchorTwo_cutoff_band`.
- An anchor-free payload staging interface now exists in root wiring:
  `RootSeedPayloadTwoNoAnchor` and its first bridge wrappers.
- Latest cycle added non-seam boundary wrappers and constructor-gap interfaces;
  remaining blocker is a missing non-seeded no-arg outside-open injectivity
  witness.
- Known blocker to avoid: constructor compositions that introduce non-frontier
  axioms (`MLC.Quadratic.external_ray_map_exists`,
  `MLC.Quadratic.bottcher_seq_converges`).
- The strict-mono seam axiom has already been removed from root frontier.
- The only remaining frontier debt is the anchor-seed axiom above.

## Where To Work

- Root orchestration: `Mlc/MainConjecture.lean`
- Main constructive monotonicity target:
  `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
- Umbrella plan and latest status:
  `plan/PLAN_axiom_elimination_status.md`

## Verification

```bash
make build && make check
```
