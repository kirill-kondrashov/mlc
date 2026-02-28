# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `██████████` **100%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ITERATION_COMPLETE`
**Target Axiom:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Last Updated:** 2026-02-28 | **Iteration:** v27
---

## Current Frontier

```bash
$ make check
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.greenRayLogGtAnchorTwo_axiom_seed
❌ Axiom frontier violation for `MLC.mlc_conjecture`.
Unexpected axioms:
- MLC.greenRayLogGtAnchorTwo_axiom_seed
```

## Active Plan Progress

| File | Scope | Progress | Left | Relevance | State |
|------|-------|----------|------|-----------|-------|
| `PLAN_axiom_elimination_status.md` | v27 orchestration + pruning + dead-end checks | `██████████` **100%** | **0%** | ⭐⭐⭐⭐⭐ | `DONE` |
| `PLAN_axiom_seed_dependency_boundary_cleanup_v27.md` | expose hidden seam-seed dependencies | `██████████` **100%** | **0%** | ⭐⭐⭐⭐⭐ | `DONE` |
| `PLAN_axiom_seed_frontier_validation_v27.md` | rebuild/check frontier after boundary cleanup | `██████████` **100%** | **0%** | ⭐⭐⭐⭐☆ | `DONE` |
| `PLAN_axiom_seed_retired_route_guardrail_v27.md` | anti-repetition guardrail | `██████████` **100%** | **0%** | ⭐⭐⭐⭐☆ | `DONE` |
| `PLAN_axiom_elimination_constructive_bridge_search_v27.md` | non-seeded proof of the remaining bridge | `██████░░░░` **62%** | **38%** | ⭐⭐⭐⭐⭐ | `STUCK` |

## Completed This Iteration

- Removed unused v26 plan files and reduced `plan/` to active v27 artifacts.
- Refactored seam dependency boundaries in Lean:
  - `greenFunctionStrictMonoAlongRayBasinTwo_of_greenRayLogGtAnchorTwoSeam`
  - `greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam`
  - made seam dependency explicit in
    `injOn_outside_open_two_of_greenFunctionStrictMonoAlongRayBasinTwoSeam`
  - updated seeded wrappers to pass explicit seam witness.
- Verified:
  - `lake build Mlc.MainConjecture` passes.
  - `make check` still isolates a single frontier axiom:
    `MLC.greenRayLogGtAnchorTwo_axiom_seed`.

## Dead-End / Self-Repetition Check

- Blocked classes remain:
  - strict subcutoff/local-window transport route
  - global proper/local degree-one route with forbidden dependencies
  - seeded replay route through `greenRayLogGtAnchorTwo_seed`
  - speculative IVT/connectedness branch
- These classes were not re-run in v27.

## Remaining Global Blocker

Constructively prove the bridge:
`DirectProperLocalWitnessTwo -> CP5ResidualLocalHomeomorphInjSeamTwo`
without invoking `greenRayLogGtAnchorTwo_seed` and without introducing any new
frontier axioms.

## Suggested Next Plans

1. Prove a non-seeded replacement for
   `greenRayUniquePreimageTwoAnchorSeam_of_greenRayLogGtAnchorTwoSeam`.
2. Build a direct non-seeded path from `DirectProperLocalWitnessTwo` to outside-open injectivity.
3. Collapse `mlc_conjecture` onto the non-seam root-tail route once (1)+(2) are complete.
