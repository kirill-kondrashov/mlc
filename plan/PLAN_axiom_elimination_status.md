# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `████████░░` **80%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Target Axiom:** `MLC.Quadratic.external_ray_map_exists`
**Last Updated:** 2026-02-28 | **Iteration:** v28
---

## Current Frontier

```bash
$ make check
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.external_ray_map_exists
❌ Axiom frontier violation for `MLC.mlc_conjecture`.
Unexpected axioms:
- MLC.Quadratic.external_ray_map_exists
```

## Active Plan Progress

| File | Scope | Progress | Left | Relevance | State |
|------|-------|----------|------|-----------|-------|
| `PLAN_axiom_elimination_status.md` | v28 orchestration + blocker tracking | `████████░░` **80%** | **20%** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom_elimination_constructive_bridge_search_v28.md` | remove non-core external-ray-data axiom dependency from root | `██████░░░░` **62%** | **38%** | ⭐⭐⭐⭐⭐ | `STUCK` |

## Completed This Iteration

- Pruned outdated completed plans from `plan/`:
  - `PLAN_axiom_seed_dependency_boundary_cleanup_v27.md`
  - `PLAN_axiom_seed_frontier_validation_v27.md`
  - `PLAN_axiom_seed_retired_route_guardrail_v27.md`
- Revalidated baseline:
  - `make build` passes.
  - `make check` now isolates only `MLC.Quadratic.external_ray_map_exists`.
- Cutover completed:
  - `MLC.mlc_conjecture` now routes through
    `mlc_conjecture_of_external_ray_map_exists_two` with
    `Quadratic.external_ray_map_exists (2 : ℂ)`.
  - `MLC.greenRayLogGtAnchorTwo_axiom_seed` no longer appears in
    `#print axioms MLC.mlc_conjecture`.
- Root swap-point isolation completed:
  - Added `externalRayMapData_two_root_frontier` and routed
    `mlc_conjecture` through it.
  - Remaining axiom elimination at root is now a one-lemma replacement.
- Root-closure bridge formalized:
  - Added wrappers from `RootClosureSubstituteTwo` to
    `Quadratic.ExternalRayMapData (2 : ℂ)` and then to `mlc_conjecture`.
  - Remaining blocker is now isolated to constructing a no-arg witness of
    `RootClosureSubstituteTwo` without non-core axioms.

## Dead-End / Self-Repetition Check

- Blocked classes remain:
  - strict subcutoff/local-window transport route
  - global proper/local degree-one route with forbidden dependencies
  - seeded replay route through `greenRayLogGtAnchorTwo_seed`
  - speculative IVT/connectedness branch
- These classes are still excluded from re-runs.

## Remaining Global Blocker

Constructively remove the remaining non-core root dependency:
`MLC.Quadratic.external_ray_map_exists`.

## Immediate Next Steps

1. Construct a core-safe no-arg witness of `Quadratic.ExternalRayMapData (2 : ℂ)`.
2. If that is blocked, build a core-safe no-arg witness of `RootClosureSubstituteTwo` and route root closure through the existing core-only wrappers.
3. Re-run `make build && make check` and keep frontier at core-only axioms.
