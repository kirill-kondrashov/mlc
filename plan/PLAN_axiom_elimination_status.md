# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `██░░░░░░░░` **20%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `CYCLE_ACTIVE`
**Target Axioms:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Last Updated:** 2026-02-27
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

## Cleanup Completed (This Iteration)

- Removed prior-cycle stuck plan file from `plan/`.
- Removed prior-cycle completed plan files from `plan/`.
- Reset active plan set to a fresh cycle focused on non-seam witness redesign.

## Plan Progress Bars

| File | Scope | Progress | Left | Effort Left | Relevance | State |
|------|-------|----------|------|-------------|-----------|-------|
| `PLAN_axiom1_noarg_greenRayUniquePreimageTwoAnchorSeam_constructor_search_v2.md` | seek no-arg constructor for unique-preimage seam via revised witness sources | `██░░░░░░░░` **20%** | **80%** | **3-10h** | ⭐⭐⭐⭐⭐ | `IN_PROGRESS` |
| `PLAN_axiom1_model_redesign_to_replace_greenRayLogGtAnchorTwoSeam_target_v1.md` | redesign model target to avoid contradictory log-gap seam requirement | `█░░░░░░░░░` **10%** | **90%** | **4-12h** | ⭐⭐⭐⭐⭐ | `READY` |
| `PLAN_axiom1_root_cutover_to_nonseam_inj_witness_interface_v1.md` | cut root theorem to non-seam injectivity witness interface | `█░░░░░░░░░` **10%** | **90%** | **3-9h** | ⭐⭐⭐⭐⭐ | `READY` |

## Dead-End / Repetition Guardrails

- Do not retry no-arg `GreenRayLogGtAnchorTwoSeam` constructor search under the
  unchanged contradictory model.
- Reject any route that introduces blocked non-frontier axioms
  (`external_ray_map_exists`, `bottcher_seq_converges`,
  `extended_ray_map_continuous`).
- If a plan branch shows no theorem-signature delta after two attempts, mark
  it `STUCK` and rotate.

## Remaining Global Blocker

- Current root path still uses a seed-backed seam boundary.
- A constructive no-arg route requires either:
  1. a non-seam injectivity witness chain, or
  2. a model redesign that replaces the contradictory log-gap seam target.

## Suggested Next Plans

1. `PLAN_axiom1_noarg_greenRayUniquePreimageTwoAnchorSeam_constructor_search_v2.md`
2. `PLAN_axiom1_model_redesign_to_replace_greenRayLogGtAnchorTwoSeam_target_v1.md`
3. `PLAN_axiom1_root_cutover_to_nonseam_inj_witness_interface_v1.md`
4. `PLAN_axiom1_constructor_inventory_for_nonseam_outside_open_injectivity_v1.md`

## Exit Condition

```bash
$ make check
All axioms used:
- Quot.sound
- propext
- Classical.choice
```

Current status: not met. Remaining frontier axiom:
- `MLC.greenRayLogGtAnchorTwo_axiom_seed`
