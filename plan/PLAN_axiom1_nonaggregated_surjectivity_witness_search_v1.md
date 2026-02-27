# Plan: Axiom 1 Nonaggregated Surjectivity Witness Search (v1)

---
**Status:** `█░░░░░░░░░` **12%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **3-8h** (roughly 80-220 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Find a surjectivity witness for the outside-open/exterior map that avoids
aggregator theorems known to pull in
`MLC.Quadratic.external_ray_map_exists`/`MLC.Quadratic.bottcher_seq_converges`.

## Work Plan

1. Isolate minimal direct surjectivity lemmas at `c = 2`.
2. Compose them with injectivity data without using blocked aggregator wrappers.
3. Add a wrapper theorem intended for root-near constructor use.
4. Verify axiom footprint of the wrapper with `Lean.collectAxioms`.

## Progress Checklist

- [x] Dead-end identified for aggregator-based composition.
- [ ] Direct nonaggregated surjectivity wrapper theorem added.
- [ ] Axiom footprint verified as frontier-safe.
- [ ] Wrapper integrated into root-near candidate path.

## Acceptance Gate

- Wrapper must avoid introducing non-core axioms beyond current frontier.
