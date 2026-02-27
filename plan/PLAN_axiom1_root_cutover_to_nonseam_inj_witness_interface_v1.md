# Plan: Axiom 1 Root Cutover To Non-Seam Inj Witness Interface (v1)

---
**Status:** `█░░░░░░░░░` **10%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `READY`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **3-9h**
**Last Updated:** 2026-02-27
---

## Objective

Cut root closure from seam-tied inputs to a non-seam outside-open injectivity
witness interface.

## Work Plan

1. Identify the narrowest existing non-seam injectivity witness interface in
   `Mlc/MainConjecture.lean`.
2. Add bridge wrappers from current root payloads to that interface.
3. Rewire root candidate wrappers to prefer non-seam interface.
4. Validate root theorem and axiom frontier behavior.

## Progress Checklist

- [x] Candidate interface identified (`RootSafeOutsideOpenInjWitnessTwo`).
- [ ] Bridge wrappers for seam-free ingress added.
- [ ] Root wrappers cut over to non-seam interface.
- [ ] `lake build Mlc.MainConjecture` passes.
- [ ] `make check` removes target axiom.

## Guardrails

- Preserve theorem signatures unless a narrower boundary is required.
- Avoid routes that require contradictory seam goals.

## Acceptance Gate

- Root candidate and closure paths are expressed through non-seam injectivity
  witness interfaces.
