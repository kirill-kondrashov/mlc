# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `███████░░░` **73%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
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

- Removed stuck plans:
  - `PLAN_axiom1_seed_isolation_payload_swap_v2.md`
  - `PLAN_axiom2_nonreal_monotonicity_argument_route.md`
- Cleaned up unused probe file:
  - deleted `check_axioms_batch.lean`
- Kept completed support plans:
  - `PLAN_root_dependency_pruning_v2.md` (`DONE`)
  - `PLAN_frontier_closure_and_cleanup.md` (`DONE`)
  - `PLAN_frontier_candidate_probe_matrix_v1.md` (`DONE`)
- Added new active plans below.

## Active Plan Set

| File | Scope | Progress | Left | Effort Left | Relevance | State |
|------|-------|----------|------|-------------|-----------|-------|
| `PLAN_axiom1_inj_witness_bootstrap_v3.md` | Eliminate `greenRayLogGtAnchorTwo_axiom_seed` | `███░░░░░░░` **30%** | **70%** | **4-8h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom2_nonreal_transport_inventory_v2.md` | Eliminate `green_function_strictMono_along_ray_basin_seam` | `████░░░░░░` **40%** | **60%** | **6-10h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_frontier_probe_inline_workflow_v2.md` | Probe/ranking workflow without persistent temp files | `█████░░░░░` **50%** | **50%** | **2-3h** | ⭐⭐⭐⭐☆ | `ACTIVE` |
| `PLAN_root_dependency_pruning_v2.md` | Root dependency pruning | `██████████` **100%** | **0%** | **0h** | ⭐⭐⭐⭐☆ | `DONE` |
| `PLAN_frontier_closure_and_cleanup.md` | Verification + guardrails + docs | `██████████` **100%** | **0%** | **0h** | ⭐⭐⭐⭐☆ | `DONE` |
| `PLAN_frontier_candidate_probe_matrix_v1.md` | Historical probe matrix snapshot | `██████████` **100%** | **0%** | **0h** | ⭐⭐⭐☆☆ | `DONE` |

## Axiom-Level Estimate

| Axiom | Progress | Left | Main Risk | Primary Plan |
|------|----------|------|-----------|--------------|
| `MLC.greenRayLogGtAnchorTwo_axiom_seed` | `███░░░░░░░` **30%** | **70%** | constructive outside-open injectivity witness still missing | `PLAN_axiom1_inj_witness_bootstrap_v3.md` |
| `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` | `████░░░░░░` **40%** | **60%** | nonreal-direction transport lemma family still incomplete | `PLAN_axiom2_nonreal_transport_inventory_v2.md` |

## Dead-End Guard (Do Not Reopen)

- Global seam target remains inconsistent:
  `not_greenRayLogGtAnchorTwoSeam`.
- Known strict-mono-free ingress dead ends remain blocked:
  `not_outsideOpenAnalyticityHypothesisTwo`,
  `not_greenFunctionDegreeOneIngressTwo`,
  `not_knownInjOnOutsideOpenSourceCandidateTwo`.

## Suggested New Plans

1. `PLAN_axiom1_inj_witness_bootstrap_v3.md`
2. `PLAN_axiom2_nonreal_transport_inventory_v2.md`
3. `PLAN_frontier_probe_inline_workflow_v2.md`

## Exit Condition

```bash
$ make check
All axioms used:
- Quot.sound
- propext
- Classical.choice
```
