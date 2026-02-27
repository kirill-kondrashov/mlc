# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `███████░░░` **74%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Target Axioms:** Both
**Last Updated:** 2026-02-27
---

## Current Frontier

```
$ make check
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.greenRayLogGtAnchorTwo_axiom_seed
- MLC.Quadratic.green_function_strictMono_along_ray_basin_seam
```

## What Changed

- Removed `STUCK` plan files from `plan/`.
- Added a new plan set focused on:
  1. retargeting Axiom 1 via direct ingress,
  2. finishing non-real monotonicity for Axiom 2,
  3. pruning root dependency surface to reduce churn.
- Kept closure/verification plan as completed.

## Active Plan Set

| File | Scope | Progress | Left | Effort Left | Relevance | State |
|------|-------|----------|------|-------------|-----------|-------|
| `PLAN_axiom1_direct_ingress_retarget.md` | Eliminate `greenRayLogGtAnchorTwo_axiom_seed` | `████░░░░░░` **35%** | **65%** | **4-8h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom2_nonreal_monotonicity_engine.md` | Eliminate `green_function_strictMono_along_ray_basin_seam` | `█████░░░░░` **45%** | **55%** | **6-10h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_root_dependency_pruning_v2.md` | Minimize root dependency fan-in | `██████░░░░` **60%** | **40%** | **2-4h** | ⭐⭐⭐⭐☆ | `ACTIVE` |
| `PLAN_frontier_closure_and_cleanup.md` | Verification + guardrails + docs | `██████████` **100%** | **0%** | **0h** | ⭐⭐⭐⭐☆ | `DONE` |

## Axiom-Level Estimate

| Axiom | Progress | Left | Main Risk | Plan Owner |
|------|----------|------|-----------|------------|
| `MLC.greenRayLogGtAnchorTwo_axiom_seed` | `████░░░░░░` **35%** | **65%** | root still threads through global anchor-gap seam family | `PLAN_axiom1_direct_ingress_retarget.md` |
| `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` | `█████░░░░░` **45%** | **55%** | constructive non-real-direction monotonicity is still missing | `PLAN_axiom2_nonreal_monotonicity_engine.md` |

## Dead-End Guard (Do Not Reopen)

- Global target `GreenRayLogGtAnchorTwoSeam` is blocked (`not_greenRayLogGtAnchorTwoSeam`); only replacement-shape seam is viable.
- Strict-mono-free ingress routes remain blocked:
  `not_outsideOpenAnalyticityHypothesisTwo`,
  `not_greenFunctionDegreeOneIngressTwo`,
  `not_knownInjOnOutsideOpenSourceCandidateTwo`.

## Suggested New Plans

1. `PLAN_axiom1_direct_ingress_retarget.md`
2. `PLAN_axiom2_nonreal_monotonicity_engine.md`
3. `PLAN_root_dependency_pruning_v2.md`

## Exit Condition

```bash
$ make check
All axioms used:
- Quot.sound
- propext
- Classical.choice
```
