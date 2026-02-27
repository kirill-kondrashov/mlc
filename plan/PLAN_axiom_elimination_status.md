# Axiom Elimination Status (Umbrella Plan)

---
**Status:** `██████████` **100%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `BATCH COMPLETE (DONE/STUCK)`
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

## What Changed This Iteration

- Ran post-Axiom2 root-near ingress inventory with `Lean.collectAxioms` probes.
- Confirmed anchor dependency is already localized to canonical seed entry path.
- Evaluated policy-exception route (`external_ray_map_exists`) and rejected it
  under current frontier policy.
- Classified remaining elimination plan as `STUCK` after no-delta repetition.
- Removed unused completed plan files from `plan/` to keep only active planning
  artifacts.

## Plan Set

| File | Scope | Progress | Left | Effort Left | Relevance | State |
|------|-------|----------|------|-------------|-----------|-------|
| `PLAN_axiom1_frontier_safe_nonseeded_ingress_search_v2.md` | frontier-safe nonseeded ingress for root | `████████░░` **82%** | **18%** | **Blocked** | ⭐⭐⭐⭐⭐ | `STUCK` |

## Ranking Delta (2026-02-27)

| Candidate | Delta | Result |
|-----------|-------|--------|
| root-near seeded aliases (`mlc_conjecture`, `rootSafeOutsideOpenInjWitnessTwo_seed`, `externalRayMapData_two_root_seed`) | `0` | still require `MLC.greenRayLogGtAnchorTwo_axiom_seed` |
| Root via `Quadratic.external_ray_map_exists (2)` | `-1/+1` | removes anchor seed but introduces `MLC.Quadratic.external_ray_map_exists` |
| Current root theorem | baseline | one remaining unexpected axiom |

## Dead-End / Repetition Check

- Repetition detected: candidate ingress set matched previous batch; probes showed
  no new frontier-safe path.
- Dead end confirmed for this batch: no assumption-free replacement removed
  `MLC.greenRayLogGtAnchorTwo_axiom_seed` without frontier expansion.

## Axiom-Level Estimate

| Axiom | Progress | Left | Main Risk | Primary Plan |
|------|----------|------|-----------|--------------|
| `MLC.greenRayLogGtAnchorTwo_axiom_seed` | `████████░░` **82%** | **18%** | no confirmed frontier-safe nonseeded ingress theorem | `PLAN_axiom1_frontier_safe_nonseeded_ingress_search_v2.md` (`STUCK`) |

## Suggested New Plans

1. `PLAN_axiom1_frontier_safe_nonseeded_ingress_search_v3.md`
2. `PLAN_axiom1_root_payload_constructor_without_anchor_v1.md`
3. `PLAN_policy_decision_external_ray_temp_allowance_v1.md` (only if policy changes)

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
