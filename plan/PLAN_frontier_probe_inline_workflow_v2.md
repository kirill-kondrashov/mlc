# Plan: Frontier Probe Inline Workflow (v2)

---
**Status:** `█████░░░░░` **50%** | **Relevance:** ⭐⭐⭐⭐☆ | **State:** `ACTIVE`
**Scope:** keep candidate-axiom ranking updated without persistent temp files
**Effort Left:** **2-3h** (roughly 40-100 Lean/Markdown LOC)
**Last Updated:** 2026-02-27
---

## Objective

Maintain a lightweight, repeatable theorem-surface ranking workflow using
inline/temporary probe commands, and feed results directly into plan updates.

## Work Plan

1. Define a stable candidate theorem list in plan notes.
2. Run `Lean.collectAxioms` probes inline each iteration.
3. Record top candidates and rejected paths in the umbrella plan.
4. Enforce "no rewrite without ranking improvement" rule.

## Progress Checklist

- [x] Candidate ranking process validated.
- [x] Rejected off-target routes documented.
- [ ] Candidate list standardized for future iterations.
- [ ] Ranking snapshot embedded in umbrella per iteration.
