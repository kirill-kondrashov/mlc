# PLAN v28-A: Constructive Bridge Search

**Status:** `██████░░░░` **62%**
**State:** `STUCK`
**Relevance:** ⭐⭐⭐⭐⭐
**Last Updated:** 2026-02-28

## Goal
Construct a frontier-safe no-arg closure route for `MLC.mlc_conjecture` by
eliminating dependency on:
`MLC.Quadratic.external_ray_map_exists`.

## Current Verified Facts

- `MLC.mlc_conjecture` now routes through
  `mlc_conjecture_of_external_ray_map_exists_two` with
  `Quadratic.external_ray_map_exists (2 : ℂ)`.
- Root frontier call is isolated at:
  `externalRayMapData_two_root_frontier`.
- Added explicit root-closure bridge wrappers in `Mlc/MainConjecture.lean`:
  - `externalRayMapData_two_of_rootClosureSubstituteTwo_of_cp5ResidualLocalHomeomorphInjSeamTwo`
  - `externalRayMapData_two_of_rootClosureSubstituteTwo`
  - `mlc_conjecture_of_rootClosureSubstituteTwo`
- Root dependency on `MLC.greenRayLogGtAnchorTwo_axiom_seed` is eliminated.
- Current `#print axioms MLC.mlc_conjecture` shows exactly one non-core axiom:
  `MLC.Quadratic.external_ray_map_exists`.
- `check_axioms.lean` allows only core axioms:
  `Quot.sound`, `propext`, `Classical.choice`.

## Blocking Gap

No frontier-safe no-arg witness of `Quadratic.ExternalRayMapData (2 : ℂ)` is
currently available without using `MLC.Quadratic.external_ray_map_exists` (or
other disallowed non-core axioms).

The root-closure bridge itself is now explicit; the remaining missing piece is a
frontier-safe no-arg witness of `RootClosureSubstituteTwo`.

## Active Work Targets

1. `RootClosureSubstituteTwo` path (preferred)
- Find a no-arg constructor chain that does not pass through seeded
  `RootSafeOutsideOpenInjWitnessTwo` wrappers.
- If impossible, formalize the exact minimal missing theorem in this chain.

2. `ExternalRayMapData` path (fallback)
- Search for a non-seeded no-arg source for
  `Quadratic.ExternalRayMapData (2 : ℂ)`.
- Reject routes that introduce non-core axioms under `check_axioms`.

## Dead-End / Self-Repetition Guardrail

Do not re-run these classes unless new ingredients appear:
- strict subcutoff/local-window transport route
- forbidden global proper/local-degree route
- seeded replay via `greenRayLogGtAnchorTwo_seed`
- speculative IVT/connectedness route

## Keep/Remove Decision

- Keep this file as the single active stuck tracker for the constructive bridge.
- Remove completed v27 subplans to keep `plan/` focused on active work only.
