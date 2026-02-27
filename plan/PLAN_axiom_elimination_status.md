# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `█████░░░░░` **55%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
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

- Removed prior stuck plan file from `plan/`.
- Removed temporary/unwired probe artifact:
  `check_axiom_probe_matrix.lean`.
- Removed completed and inactive plan files from `plan/`.

## Active Plan Set

| File | Scope | Progress | Left | Effort Left | Relevance | State |
|------|-------|----------|------|-------------|-----------|-------|
| `PLAN_axiom1_constructor_family_min_cut_probe_v1.md` | identify minimal constructor-family cut that can replace seeded seam usage | `█░░░░░░░░░` **10%** | **90%** | **3-7h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom1_surj_target_reformulation_without_externalRayMapData_v1.md` | reformulate root chain around direct surj/inj payloads | `█░░░░░░░░░` **8%** | **92%** | **4-9h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |
| `PLAN_axiom1_root_boundary_cutover_guardrail_matrix_v1.md` | prevent repetitive/dead-end root rewires with explicit guardrails | `█░░░░░░░░░` **6%** | **94%** | **2-6h** | ⭐⭐⭐⭐⭐ | `ACTIVE` |

## Axiom-Level Estimate

| Axiom | Progress | Left | Main Risk | Primary Plan |
|------|----------|------|-----------|--------------|
| `MLC.greenRayLogGtAnchorTwo_axiom_seed` | `█████████░` **86%** | **14%** | no assumption-free constructive seam closure yet | `PLAN_axiom1_constructor_family_min_cut_probe_v1.md` |

## Dead-End Guard (Do Not Repeat)

- Do not reopen cutoff-band seam route
  (`not_greenRayLogGtAnchorTwo_cutoff_band`).
- Do not retry preimage-seam-to-anchor implication
  (`not_greenRayLogGtAnchorTwoSeam_of_greenRayAnchorThresholdPreimageTwoSeam`).
- Do not accept rewires that add non-frontier axioms
  (`MLC.Quadratic.external_ray_map_exists`,
  `MLC.Quadratic.bottcher_seq_converges`,
  `MLC.Quadratic.extended_ray_map_continuous`).

## New Plan Suggestions

1. `PLAN_axiom1_assumption_free_closure_candidate_search_v1.md`
2. `PLAN_axiom1_greenRay_anchor_gap_constructive_bridge_v1.md`
3. `PLAN_axiom1_root_unconditional_wrapper_min_signature_v1.md`

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
