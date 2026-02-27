# Plan: Axiom 1 Injectivity-Witness Bootstrap (v3)

---
**Status:** `███░░░░░░░` **30%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **4-8h** (roughly 100-220 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Route `mlc_conjecture` through a root theorem requiring only an explicit
outside-open injectivity witness and then construct that witness without using
the anchor-gap axiom path.

## Work Plan

1. Keep root path anchored at
   `mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_seed`.
2. Build a constructive candidate for `RootSafeOutsideOpenInjWitnessTwo`.
3. Avoid any path that reintroduces `greenRayLogGtAnchorTwo_seed`.
4. Re-run `lake build Mlc.MainConjecture` and `make check`.

## Progress Checklist

- [x] Root path already split to witness-seeded boundary.
- [ ] Constructive witness theorem implemented (axiom-free for Axiom 1).
- [ ] Root theorem instance switched to constructive witness.
- [ ] `make check` no longer lists `MLC.greenRayLogGtAnchorTwo_axiom_seed`.
