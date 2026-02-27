# Plan: Axiom 1 Surjectivity Target Reformulation Without ExternalRayMapData (v1)

---
**Status:** `█░░░░░░░░░` **8%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **4-9h** (roughly 120-280 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Reformulate the root-target path so it can terminate through direct
injectivity+surjectivity payloads, avoiding dependency on
`ExternalRayMapData`-shaped root wrappers wherever possible.

## Work Plan

1. Isolate the minimal theorem boundary where `ExternalRayMapData` first becomes required.
2. Introduce an alternate boundary theorem expressed only in direct surj/inj terms.
3. Rewire one root-candidate chain to the alternate boundary.
4. Validate theorem usability and axiom footprint on the rewired chain.

## Progress Checklist

- [x] Existing nonaggregated surjectivity bridge inventory reused from prior cycle.
- [ ] Alternate direct surj/inj boundary theorem added.
- [ ] One root-candidate chain rewired to that boundary.
- [ ] Rewired chain passes frontier guard (no new non-core axioms).

## Acceptance Gate

- At least one root-candidate route reaches `LocallyConnectedSpace mandelbrotSet`
  without introducing a new `ExternalRayMapData` dependency edge.
