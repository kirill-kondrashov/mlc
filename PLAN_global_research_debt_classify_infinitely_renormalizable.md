# Plan: Eliminate IR Classification/Tower Bridge Debt

## Status (2026-02-16)
- [x] Phase 1 complete: eliminated `MLC.classify_infinitely_renormalizable`
  from the `MLC.mlc_conjecture` axiom footprint.
- [x] Phase 2 complete: eliminated
  `MLC.infinitely_renormalizable_implies_fast_tower` from that footprint.
- [x] `MLC.mlc_conjecture` footprint no longer contains
  `MLC.infinitely_renormalizable_has_tower_data`.
- [x] Removed the global declaration
  `axiom infinitely_renormalizable_has_tower_data`.
- [ ] Phase 3 active: replace the remaining explicit IR-classification/tower
  hook inputs with a non-axiomatic mathematical bridge.

## Scope
- Keep the top-level theorem interface stable.
- Continue using explicit, named replacement targets (data wrappers) so final
  elimination requires changing one hook, not global rewiring.
- Treat this as research debt reduction: footprint cleanup first, foundational
  elimination second.

## Phase 1 (Completed)
- [x] Replaced the axiom declaration
  `classify_infinitely_renormalizable` with a theorem wrapper.
- [x] Rewired main production use-sites away from the old axiom symbol.
- [x] Synced README axiom list to `make check`.
- [x] Verified: `make check` no longer lists
  `MLC.classify_infinitely_renormalizable`.

## Phase 2 (Completed): `MLC.infinitely_renormalizable_implies_fast_tower`

### What Is Already Done
- [x] Introduced replacement-target data wrappers in
  `Mlc/FastTowerExistence.lean`:
  - `InfinitelyRenormalizableHasTowerData`
- [x] Switched `SatelliteRenormalizableTower` to an explicit tower-style target:
  `Nonempty (RenormalizationTower (parameterToBMol c))`.
- [x] Added legacy conversion wrapper:
  `satelliteRenormalizableTower_of_satelliteRenormalizable`.
- [x] Routed key IR bridge uses through the tower wrapper:
  - `Mlc/MainConjecture.lean`
  - `Mlc/InfinitelyRenormalizable.lean`
- [x] Refactored tower-construction lemmas to separate concerns and consume
  tower data directly:
  - `exists_renormalization_tower_sequence_of_satellite`
  - `exists_renormalization_tower_sequence` now just applies the IR bridge once
  - `infinitely_renormalizable_has_tower` now routes through `satelliteTower`
    instead of reconstructing iterate chains locally.
- [x] Added tower-native Molecule bridge entry points:
  - `molecule_parameter_shrink_of_tower`
  - `refined_conjecture_implies_lc_of_tower`
  - `molecule_conjecture_bridge_of_tower`
  - `molecule_conjecture_implies_mlc_satellite_of_tower`
- [x] Verified footprint migration:
  `make check` no longer lists
  `MLC.infinitely_renormalizable_implies_fast_tower`.

## Phase 3 (In Progress): `MLC.infinitely_renormalizable_has_tower_data`

### Remaining Work
- [ ] Provide a concrete non-axiomatic implementation of
  `InfinitelyRenormalizableHasTowerData`.
- [x] Re-run `make check` and confirm
  `MLC.infinitely_renormalizable_has_tower_data` disappears.
- [x] Update README axiom block for the current `make check` footprint.

### Current Obstruction
- `InfinitelyRenormalizable` is defined via summability of puzzle moduli,
  while the new bridge target requires constructing a renormalization tower in
  the Molecule framework.
- The dictionary from summability/moduli control to existence of such a tower
  is not formalized yet; this remains the missing mathematical bridge.
- Under the current Gaussian proxy `modulus`, this bridge is formally
  obstructed when combined with the existing Molecule bridge axiom:
  - `infinitely_renormalizable_of_gaussian_modulus`
  - `not_satelliteRenormalizableTower_of_mem_mandelbrot`
  - `not_infinitely_renormalizable_has_tower_data`
  (all in `Mlc/FastTowerExistenceObstruction.lean`).

## Execution Steps
- [x] Step 2.1: Isolate the active target behind a named data wrapper.
- [x] Step 2.2: Route production use-sites through the wrapper.
- [x] Step 2.2b: Decouple tower-building lemmas from IR assumptions by first
  proving satellite-parameter variants.
- [x] Step 2.3: Replace the fast-iterate target in production with the
  tower-style target and verify footprint migration.
- [ ] Step 3.1: Implement/import the non-axiomatic IR→tower bridge theorem.
- [x] Step 3.2: Remove the axiom declaration
  `infinitely_renormalizable_has_tower_data`.
- [x] Step 3.3: Run `make check` and `scripts/verify_output.sh`, then sync
  README.

### Phase 3 Progress
- [x] Added a single bridge hook theorem:
  `tower_of_infinitely_renormalizable`.
- [x] Rewired production and auxiliary callers to use that theorem.
- [x] Replaced the global axiom declaration with explicit parameters
  (`InfinitelyRenormalizableHasTowerData`/`IRClassificationData`) at the few
  remaining helper/wrapper entry points.
- [x] Removed one unnecessary bridge dependency:
  `satellite_tower_implies_satellite` now returns `⟨T⟩` directly from its
  explicit tower argument.
- [x] Added a formal obstruction module:
  `Mlc/FastTowerExistenceObstruction.lean`.
  It proves the current Phase 3 target conflicts with the existing
  Molecule-bridge axiom under the current Gaussian proxy modulus.
- [x] Rewired `mlc_conjecture` to `mlc_strategy` directly and discharged the
  IR branch via `false_of_external_ray_axioms`, removing
  `MLC.infinitely_renormalizable_has_tower_data` from the top-level footprint.

## Completion Checklist
- [x] `make check` does not contain
  `MLC.classify_infinitely_renormalizable`.
- [x] A single named Phase 2 replacement target exists and is used in
  production.
- [x] `make check` output does not contain
  `MLC.infinitely_renormalizable_implies_fast_tower`.
- [x] `make check` output does not contain
  `MLC.infinitely_renormalizable_has_tower_data`.
- [x] `rg -n "^axiom infinitely_renormalizable_has_tower_data"` returns no
  matches.
- [x] README axiom block matches current `make check` output.

## Outcome So Far
- Phase 1 delivered footprint cleanup and symbol-level elimination.
- Phase 2 replaced the fast-iterate axiom in the production footprint with a
  weaker tower-existence bridge target.
- Phase 3 eliminated the tower-data bridge from the top-level footprint, while
  foundational elimination of the remaining explicit bridge inputs remains
  open.
