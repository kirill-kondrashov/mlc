# Plan: Axiom 1 Root Boundary Cutover Guardrail Matrix (v1)

---
**Status:** `█░░░░░░░░░` **6%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **2-6h** (roughly 70-180 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Construct a guardrail matrix for root-boundary rewires so each attempted cutover
is pre-checked against repetition/dead-end signatures before code changes.

## Work Plan

1. List all root-entry wrappers that can feed `mlc_conjecture`.
2. Tag each wrapper by assumption class (seeded seam, seam-parameterized, direct witness).
3. Mark forbidden/known-dead routes and blocked axiom expansions.
4. Publish a one-step cutover order that only allows non-repetitive attempts.

## Progress Checklist

- [x] Current root-entry wrapper location and seeded split boundary confirmed.
- [ ] Wrapper classification matrix completed.
- [ ] Dead-end signatures encoded as explicit reject criteria.
- [ ] Ordered cutover queue published for next implementation cycle.

## Acceptance Gate

- Every future root cutover attempt must map to a matrix row and pass all
  guardrail checks before implementation.
