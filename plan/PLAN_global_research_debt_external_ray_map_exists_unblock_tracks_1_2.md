# Plan: Unblock `external_ray_map_exists` Elimination via Track 1 + Track 2

Date: 2026-02-20

## Goal
Eliminate `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
`MLC.mlc_conjecture` without:
- introducing new axioms,
- adding hypotheses to `MLC.mlc_conjecture`,
- collapsing the proof into tautological contradiction routing.

## Why previous path was blocked
Current model contains an explicit incompatibility:
- `MoleculeConformalModulusLowerBoundData -> ¬ InfinitelyRenormalizableHasTowerData`
  (`Mlc/FastTowerExistenceObstruction.lean`).
So any architecture that tries to constructively assume both global
`InfinitelyRenormalizableHasTowerData` and conformal bridge data is blocked.

## Track 1 (IR Classification, constructive)
Target: produce
`IRClassificationData :=
  ∀ c hc hIR, PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c`
without using global `InfinitelyRenormalizableHasTowerData`.

### Scope
- Build a local, per-parameter classification route for IR parameters.
- Keep finite branch via Yoccoz path unchanged.
- Do not use contradiction as the provider in final active path.

### Deliverables
1. New constructive provider theorem for `IRClassificationData` (or an equivalent
   theorem consumed directly by `mlc_strategy_of_branchLocalData`).
2. No dependence of that provider on
   `InfinitelyRenormalizableHasTowerData`.
3. `make check` still reports only core axioms plus remaining external-ray seam
   until Track 2 is complete.

## Track 2 (Satellite bridge, constructive)
Target: provide constructive
`h_bridge : MoleculeConjectureRefined -> ... -> LocallyConnectedAt ...`
without contradiction providers in `Mlc/MainConjecture.lean`.

### Scope
- Prefer direct bridge construction into `mlc_conjecture_of_motionHyp_classify_bridge_data`.
- Avoid reintroducing removed axioms through hidden wrappers.
- Keep all introduced declarations on the rooted `mlc_conjecture` path.

### Deliverables
1. Constructive bridge provider theorem with explicit dependencies.
2. Active `mlc_conjecture` path no longer obtains bridge data from `False.elim`.
3. Rooted dependency audit clean: no unused declarations in
   `Mlc/MainConjecture.lean`.

## Baseline Refactor Completed (this commit series)
To avoid spinning around the inconsistent pair interface, the active fallback
in `Mlc/MainConjecture.lean` is now routed directly through:
- `mlc_conjecture_of_motionHyp_classify_bridge_data`,
and no longer through a bundled `(tower + conformal)` wrapper theorem.

This keeps the remaining replacement targets explicit:
1. constructive `IRClassificationData`,
2. constructive `h_bridge`.

## Progress (2026-02-20)
- [x] Track-1 interface extraction in `Mlc/MainConjecture.lean`:
  - added `IRNoTowerImpliesPrimitiveData`;
  - added
    `irClassificationData_of_noTowerImpliesPrimitiveData :
      IRNoTowerImpliesPrimitiveData -> IRClassificationData`;
  - added
    `mlc_conjecture_of_motionHyp_noTowerImpliesPrimitive_moleculeBridgeTarget`
    and rewired the active fallback to consume this Track-1 target directly.
  This removes dependence on opaque pre-packed `IRClassificationData` at the
  fallback boundary and makes the remaining constructive classification
  obligation explicit.
- [x] Centralized Track-1 classification theorem in
  `Mlc/InfinitelyRenormalizable.lean`:
  - added `classify_infinitely_renormalizable_of_noTowerImpliesPrimitive`;
  - rewired `Mlc/MainConjecture.lean` to derive `IRClassificationData`
    through that theorem.
  This keeps Track-1 logic in the IR module rather than duplicating the
  by-cases proof in `MainConjecture`.
- [x] Combined Track-1 + Track-2 seam packaging in `Mlc/MainConjecture.lean`:
  - added
    `IRNoTowerPrimitiveAndMoleculeBridgeTargetData :=
      IRNoTowerImpliesPrimitiveData ∧
      MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData`;
  - added `mlc_conjecture_of_motionHyp_track12_data`;
  - rewired the active fallback to consume this single combined seam datum.
  This reduces replacement surface area and makes remaining obligations explicit
  as one packaged target.
- [x] Added an explicit Track-2 assembly theorem in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_motionHyp_classify_moleculeBridgeTarget`
  consuming `MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData`.
- [x] Fixed a regression where direct use of
  `MoleculeBridgeTarget.bridge_of_moleculeBridgeTarget` reintroduced
  `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
  The active bridge now uses `lc_at_of_shrink_of_connected_at` with
  `finite_connectedAt_provider_of_motionHyp`, preserving the current
  one-axiom frontier.
- [x] `make build`, `make graphs`, `make check`, and
  `scripts/verify_output.sh` pass after rewiring.

## Execution Order
1. Implement Track 1 provider interface and prove as much non-axiomatically as
   possible.
2. Implement Track 2 provider interface and wire it into the same assembly
   theorem.
3. Rewire `mlc_conjecture` path to consume constructive Track 1 + Track 2
   providers.
4. Remove contradiction fallbacks from rooted path.
5. Verify with:
   - `make build`
   - `make graphs`
   - `make check`
   - `scripts/verify_output.sh`

## Immediate Theorem Targets
1. Track 1:
   prove `IRNoTowerImpliesPrimitiveData` constructively in
   `Mlc/InfinitelyRenormalizable.lean` (without
   `InfinitelyRenormalizableHasTowerData`).
2. Track 2:
   prove `MoleculeBridgeTarget.MoleculeImpliesSatellitePrincipalNestData`
   constructively (or via a proved stronger target with a theorem-level
   reduction), then wire it into `mlc_conjecture_of_motionHyp_track12_data`
   without `False.elim`.

## Exit Criteria
- `MLC.Quadratic.external_ray_map_exists` removed from `MLC.mlc_conjecture`
  axiom footprint.
- No contradiction-only provider in transitive dependencies of
  `MLC.mlc_conjecture`.
- No new axioms, no new hypotheses on `MLC.mlc_conjecture`.
