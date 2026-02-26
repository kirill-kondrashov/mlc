# MLC Formalization Status

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph (rooted at `MLC.mlc_conjecture`)](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository is a Lean formalization scaffold centered on `MLC.mlc_conjecture`.
The code compiles and `MLC.mlc_conjecture` is `sorry`-free.

## Current Axiom Frontier (`make check`)

As of 2026-02-26, exactly two non-core axioms remain in the root theorem:

- `MLC.greenRayLogGtAnchorTwo_axiom_seed`
- `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`

Expected output:

```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.greenRayLogGtAnchorTwo_axiom_seed
- MLC.Quadratic.green_function_strictMono_along_ray_basin_seam
```

## Progress Snapshot (Effort In Hours, Not Weeks)

| Target Axiom | Progress | Left | Estimated Remaining Effort |
|---|---|---|---|
| `greenRayLogGtAnchorTwo_axiom_seed` | `█████████░` 90% | 10% | ~15-30 Lean LOC, ~0.5-1.5 hrs |
| `green_function_strictMono_along_ray_basin_seam` | `█████░░░░░` 46% | 54% | ~120-200 Lean LOC, ~4-8 hrs |

Total estimated remainder: ~135-230 Lean LOC, ~5-9 hours.

## Active Plans (`plan/*`)

| File | Relevance | Progress | Left | Estimated Remaining Effort |
|---|---|---|---|---|
| `plan/PLAN_axiom_elimination_status.md` | ⭐⭐⭐⭐⭐ | `██████░░░░` 56% | 44% | ~5-9 hours |
| `plan/PLAN_exists_ray_preimage_green_pos_seam_replacement.md` | ⭐⭐⭐⭐⭐ | `█████████░` 90% | 10% | ~15-30 LOC, 0.5-1.5 hrs |
| `plan/PLAN_prove_green_function_radial_monotonicity.md` | ⭐⭐⭐⭐⭐ | `██░░░░░░░░` 18% | 82% | ~120-200 LOC, 4-8 hrs |
| `plan/PLAN_green_function_ray_inversion_c2.md` | ⭐⭐⭐⭐ | `██████░░░░` 57% | 43% | ~70-110 LOC, 2-4 hrs |
| `plan/PLAN_eliminate_green_function_strictMono_along_ray_basin_seam.md` | ⭐⭐⭐⭐⭐ | `██████░░░░` 58% | 42% | ~90-130 LOC, 2-4 hrs |
| `plan/PLAN_basin_monotonicity_practical_way_forward.md` | ⭐⭐⭐ | `███████░░░` 68% | 32% | ~30-60 LOC, 1-2 hrs |

## Key Technical Reality

- The old global anchor-gap seam is inconsistent in the current model:
  `not_greenRayLogGtAnchorTwoSeam`.
- This means Axiom 1 is a seam-replacement/wiring task (small).
- The dominant remaining proof debt is Axiom 2 (strict radial monotonicity at `c = 2`).

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
