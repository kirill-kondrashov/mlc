# Plan: Axiom 1 Frontier-Safe Nonseeded Ingress Search (v2)

---
**Status:** `████████░░` **82%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `STUCK`
**Axiom Target:** `MLC.greenRayLogGtAnchorTwo_axiom_seed`
**Effort Left:** **Blocked pending a new frontier-safe theorem route**
**Last Updated:** 2026-02-27
---

## Objective

Find a replacement ingress for `MLC.mlc_conjecture` that removes
`greenRayLogGtAnchorTwo_axiom_seed` without introducing
`MLC.Quadratic.external_ray_map_exists`.

## Iteration Results (2026-02-27)

- Refreshed root-near candidate inventory after Axiom-2 removal.
- `Lean.collectAxioms` probes confirm root-near seeded candidates still depend on
  `MLC.greenRayLogGtAnchorTwo_axiom_seed`:
  - `MLC.mlc_conjecture`
  - `MLC.mlc_conjecture_of_rootSafeOutsideOpenInjWitnessTwo_seed`
  - `MLC.rootSafeOutsideOpenInjWitnessTwo_seed`
  - `MLC.externalRayMapData_two_root_seed`
  - `MLC.rootSeedPayloadTwo_strictMono_seeded`
- Constructor theorems for `RootSeedPayloadTwo` are core-only but require
  assumptions that still include the anchor seam as input.
- Exception route (`Quadratic.external_ray_map_exists (2)`) removes anchor seed
  but adds `MLC.Quadratic.external_ray_map_exists` (policy violation).

## Progress Checklist

- [x] Prior stuck Axiom-1 plan removed.
- [x] Candidate ingress inventory refreshed for post-Axiom2 state.
- [x] Frontier-safe candidate search executed with axiom probes.
- [ ] Frontier-safe candidate identified (blocked).
- [ ] Root rewired to frontier-safe nonseeded ingress (blocked).
- [ ] `make check` no longer lists `MLC.greenRayLogGtAnchorTwo_axiom_seed`.

## Stuck Reason

- Current candidate set is self-repeating with no frontier delta.
- No assumption-free frontier-safe nonseeded ingress theorem was found.
- Any immediate replacement introduces a disallowed frontier axiom.

## Acceptance Gate

- Any route that adds `MLC.Quadratic.external_ray_map_exists` is non-admissible.
