# Plan: Axiom 1 Constructor Family Min-Cut Probe (v1)

---
**Status:** `█░░░░░░░░░` **10%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **3-7h** (roughly 90-240 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Find the smallest constructor-family cut that can replace seeded
`GreenRayLogGtAnchorTwoSeam` usage with a provable non-seeded premise while
preserving frontier safety (`-1/+0`).

## Work Plan

1. Enumerate seam-parameterized constructors that are already `-1/+0`.
2. Partition them by required hypotheses and identify minimal assumption sets.
3. Add/adjust bridge lemmas to target one minimal family as the main cutover.
4. Re-run axiom footprint checks for each bridge candidate.

## Progress Checklist

- [x] Baseline `-1/+0` constructor families identified from prior probe results.
- [ ] Minimal assumption-set ranking completed.
- [ ] At least one bridge lemma drafted for the top-ranked family.
- [ ] Candidate validated as frontier-safe under `Lean.collectAxioms`.

## Acceptance Gate

- One constructor family must be selected with a concrete proof target that can
  remove seeded seam instantiation from the root closure path.
