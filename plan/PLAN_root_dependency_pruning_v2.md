# Plan: Root Dependency Pruning v2

---
**Status:** `██████░░░░` **60%** | **Relevance:** ⭐⭐⭐⭐☆ | **State:** `ACTIVE`
**Scope:** minimize root theorem dependency surface for faster axiom elimination
**Effort Left:** **2-4h** (roughly 60-140 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Shrink the dependency fan-in of `mlc_conjecture` so each remaining frontier
axiom is swapped at one explicit seam only.

## Work Plan

1. Introduce/keep single-purpose seed aliases for each root dependency.
2. Ensure `mlc_conjecture` calls only one root bundle constructor.
3. Route deep helper chains through parameterized seams instead of global seeds.
4. Add local comments marking replacement points for Axiom 1 and Axiom 2.
5. Re-check with `make check` after each pruning step.

## Progress Checklist

- [x] Root theorem is already funneled through root-seed payload wrappers.
- [x] Many branch-specific ingress routes are isolated from the root theorem.
- [ ] Single replacement point for Axiom 1 confirmed by `rg` call graph pass.
- [ ] Single replacement point for Axiom 2 confirmed by `rg` call graph pass.
- [ ] Residual helper aliases not on root path removed.

## Done Criteria

- Axiom elimination edits become local (one seam per axiom) without broad churn.
- `plan/` progress can advance without reopening superseded ingress branches.
