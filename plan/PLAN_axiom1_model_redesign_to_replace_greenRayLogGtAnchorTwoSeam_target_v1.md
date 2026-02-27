# Plan: Axiom 1 Model Redesign To Replace GreenRayLogGtAnchorTwoSeam Target (v1)

---
**Status:** `█░░░░░░░░░` **10%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `READY`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **4-12h**
**Last Updated:** 2026-02-27
---

## Objective

Redesign the root-side seam target to avoid direct dependence on
`GreenRayLogGtAnchorTwoSeam`, which is contradictory in the current model.

## Work Plan

1. Identify the minimal theorem interface where log-gap seam is required.
2. Propose replacement interface based on non-seam injectivity/surjectivity
   witnesses.
3. Build compatibility bridge theorems from existing constructive payloads.
4. Verify no new frontier axioms are introduced.

## Progress Checklist

- [x] Contradiction boundary identified (`not_greenRayLogGtAnchorTwoSeam`).
- [ ] Minimal replacement interface specified.
- [ ] Bridge theorem family added.
- [ ] Root candidate path compiles through redesigned interface.
- [ ] `make check` removes target axiom.

## Guardrails

- Keep replacement interface strictly weaker or equivalent to current use.
- Reject broad redesigns that expand axiom surface.

## Acceptance Gate

- Root path no longer requires `GreenRayLogGtAnchorTwoSeam` as a target.
