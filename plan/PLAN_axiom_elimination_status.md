# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `██░░░░░░░░` **24%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
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

## Cleanup Applied

- Removed `STUCK` plan files from `plan/`.
- Removed stale completed per-cycle plan files that were no longer active.
- Kept actionable history in code and README; restarted with a fresh active set.

## Active Plan Set

| File | Scope | Progress | Left | Effort Left | Relevance | State |
|------|-------|----------|------|-------------|-----------|-------|
| `PLAN_axiom1_frontier_delta_probe_matrix_v1.md` | find candidate branch with frontier delta `-1/+0` | `██░░░░░░░░` **16%** | **84%** | **2-5h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom1_nonaggregated_surjectivity_witness_search_v1.md` | construct surjectivity witness without blocked aggregators | `█░░░░░░░░░` **12%** | **88%** | **3-8h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom1_root_single_boundary_cutover_after_delta_minus_one_v1.md` | cut root at one boundary once admissible candidate exists | `█░░░░░░░░░` **8%** | **92%** | **2-5h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |

## Axiom-Level Estimate

| Axiom | Progress | Left | Main Risk | Primary Plan |
|------|----------|------|-----------|--------------|
| `MLC.greenRayLogGtAnchorTwo_axiom_seed` | `████████░░` **82%** | **18%** | no validated `-1/+0` constructor yet | `PLAN_axiom1_frontier_delta_probe_matrix_v1.md` |

## Dead-End Guard (Do Not Repeat)

- Do not reopen cutoff-band seam route
  (`not_greenRayLogGtAnchorTwo_cutoff_band`).
- Do not retry preimage-seam-to-anchor implication
  (`not_greenRayLogGtAnchorTwoSeam_of_greenRayAnchorThresholdPreimageTwoSeam`).
- Do not accept rewires that add non-frontier axioms
  (`MLC.Quadratic.external_ray_map_exists`,
  `MLC.Quadratic.bottcher_seq_converges`,
  `MLC.Quadratic.extended_ray_map_continuous`).

## Suggested New Plans (If This Cycle Stalls)

1. `PLAN_axiom1_constructor_family_min_cut_probe_v1.md`
2. `PLAN_axiom1_surj_target_reformulation_without_externalRayMapData_v1.md`
3. `PLAN_axiom1_root_boundary_cutover_guardrail_matrix_v1.md`

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
