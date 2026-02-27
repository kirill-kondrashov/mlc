# Plan: Axiom 1 Root Single-Boundary Cutover After Delta Minus One (v1)

---
**Status:** `█░░░░░░░░░` **8%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **2-5h** (roughly 50-130 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Once a frontier-safe constructor candidate is proven (`-1/+0`), perform a single
boundary cutover so `MLC.mlc_conjecture` no longer enters via seeded anchor
wrappers.

## Work Plan

1. Select one admissible candidate from probe matrix output.
2. Replace the smallest root alias boundary body with that candidate.
3. Keep public theorem signatures stable where feasible.
4. Validate with `make build`, `make check`, and root-near probe set.

## Progress Checklist

- [x] Root ingress boundary location identified.
- [ ] Frontier-safe candidate selected from probe matrix.
- [ ] Boundary cutover patch applied.
- [ ] `make check` no longer lists `MLC.greenRayLogGtAnchorTwo_axiom_seed`.

## Acceptance Gate

- Root theorem remains `sorry`-free and frontier-core-only.
