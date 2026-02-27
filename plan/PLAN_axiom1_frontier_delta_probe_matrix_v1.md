# Plan: Axiom 1 Frontier Delta Probe Matrix (v1)

---
**Status:** `██░░░░░░░░` **16%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **2-5h** (roughly 60-140 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Systematically enumerate and probe root-near constructor candidates, keeping only
paths with frontier delta `-1/+0` (remove anchor seed, add no non-core axioms).

## Work Plan

1. Build a probe matrix of root-near theorem candidates.
2. Run `Lean.collectAxioms` on each candidate.
3. Rank candidates by frontier delta and prune dominated paths.
4. Export a shortlist of admissible cutover targets.

## Progress Checklist

- [x] Seeded and seam-free constructor families inventoried.
- [ ] Probe matrix script updated with new candidates.
- [ ] At least one candidate with delta `-1/+0` found.
- [ ] Candidate shortlist handed off to cutover plan.

## Acceptance Gate

- Candidate set must include at least one frontier-safe cutover target.
