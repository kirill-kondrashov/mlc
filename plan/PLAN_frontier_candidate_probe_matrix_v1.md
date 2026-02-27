# Plan: Frontier Candidate Probe Matrix (v1)

---
**Status:** `██████████` **100%** | **Relevance:** ⭐⭐⭐⭐☆ | **State:** `DONE`
**Scope:** rank theorem-entry candidates by axiom surface and replacement cost
**Effort Left:** **0h**
**Last Updated:** 2026-02-27
---

## Objective

Keep progress non-repetitive by maintaining a ranked matrix of candidate root
ingress theorems and their exact axiom footprints.

## Work Plan

1. Keep a scripted `Lean.collectAxioms` batch for candidate theorems.
2. Record candidate ranking in plan notes after each iteration.
3. Promote only candidates with strictly smaller frontier dependency.
4. Use ranking results to decide next code edits (avoid dead-end churn).

## Progress Checklist

- [x] Batch probe workflow validated; temporary script removed during cleanup.
- [x] Candidate matrix written (top entries below).
- [x] Root theorem path validated against best current candidate.
- [x] Dead-end/repetition flags attached to rejected candidates.

## Candidate Matrix (Current Iteration)

| Rank | Theorem | Non-baseline axioms | Off-target axioms | Notes |
|------|---------|----------------------|-------------------|-------|
| 1 | `MLC.mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_seed` | 1 (`greenRayLogGtAnchorTwo_axiom_seed`) | 0 | Best currently exposed root wrapper (requires external injectivity witness input). |
| 2 | `MLC.mlc_conjecture` | 2 (both frontier targets) | 0 | Current exported theorem. |
| 3 | `MLC.rootSafeOutsideOpenInjWitnessTwo_seed` | 2 (both frontier targets) | 0 | Supplies the witness consumed by rank-1 theorem. |
| 4 | `MLC.external_ray_map_exists_two_constructive` | 2 (both frontier targets) | 0 | Same frontier as root theorem. |
| 5 | `MLC.injOn_outside_open_two_axiom_seed` | 1 | 1 (`MLC.Quadratic.external_ray_map_exists`) | Rejected: introduces off-target axiom. |

## Dead-End / Repetition Flags

- Rejected for frontier purity:
  `MLC.injOn_outside_open_two_axiom_seed` (adds off-target axiom).
- No candidate currently improves over rank-1 without requiring unavailable
  constructive witness data.
- Repetition rule: do not re-run broad root rewires unless a candidate strictly
  reduces non-baseline count and keeps off-target count at zero.
