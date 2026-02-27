# Plan: Eliminate `greenRayLogGtAnchorTwo_axiom_seed` via Direct Ingress Retarget

---
**Status:** `████░░░░░░` **35%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **4-8h** (roughly 120-220 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Remove root dependence on `GreenRayLogGtAnchorTwoSeam` by rerouting `mlc_conjecture`
through direct constructive ingress predicates already present in the file:

- `DirectProperLocalWitnessTwo`
- `DynamicalBottcherConformalIdentificationTwo`
- `RemainingConstructiveIngressTwo`

## Why This Plan

- The old global seam target is inconsistent (`not_greenRayLogGtAnchorTwoSeam`).
- Rewiring wrappers around that seam is no longer a productive elimination path.

## Work Plan

1. Trace all uses of `greenRayLogGtAnchorTwo_seed` that are reachable from
   `mlc_conjecture`.
2. Introduce a new root payload centered on direct ingress witnesses instead of
   global anchor-gap seam assumptions.
3. Repoint the root theorem route to
   `mlc_conjecture_of_remainingConstructiveIngressTwo`-style endpoints.
4. Keep old seam-based lemmas for compatibility, but remove them from root path.
5. Re-run `lake build Mlc.MainConjecture` and `make check`.

## Progress Checklist

- [x] Inconsistent old seam target formally identified.
- [x] Alternative direct-ingress theorem family already present.
- [ ] Root payload type switched off global anchor-gap seam.
- [ ] `mlc_conjecture` route detached from `greenRayLogGtAnchorTwo_seed`.
- [ ] `make check` no longer lists `MLC.greenRayLogGtAnchorTwo_axiom_seed`.

## Done Criteria

- Root theorem dependency graph no longer reaches `greenRayLogGtAnchorTwo_axiom_seed`.
- `make check` frontier drops Axiom 1.
