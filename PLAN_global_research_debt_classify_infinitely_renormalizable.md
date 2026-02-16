# Plan: Eliminate IR Classification/Fast-Tower Bridge Debt

## Status (2026-02-16)
- [x] Phase 1 complete: eliminated `MLC.classify_infinitely_renormalizable`
  from the `MLC.mlc_conjecture` axiom footprint.
- [x] Phase 2 active: eliminate
  `MLC.infinitely_renormalizable_implies_fast_tower` from that footprint.
- [x] `make check` currently reports the Phase 2 target axiom explicitly.

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

## Phase 2 (In Progress): `MLC.infinitely_renormalizable_implies_fast_tower`

### What Is Already Done
- [x] Introduced a minimal replacement-target data wrapper in
  `Mlc/FastTowerExistence.lean`:
  - `InfinitelyRenormalizableImpliesSatelliteData`
  - `infinitely_renormalizable_implies_satellite_data_via_axiom`
- [x] Routed key IR bridge uses through that wrapper:
  - `Mlc/MainConjecture.lean`
  - `Mlc/InfinitelyRenormalizable.lean`
- [x] Collapsed direct production references to
  `infinitely_renormalizable_implies_fast_tower` down to the axiom declaration
  plus the single wrapper constructor site.
- [x] Refactored tower-construction lemmas to separate concerns:
  - `exists_renormalization_tower_sequence_of_satellite`
  - `exists_renormalization_tower_sequence` now just applies the IR bridge once
  - `infinitely_renormalizable_has_tower` now routes through `satelliteTower`
    instead of reconstructing iterate chains locally.
- [x] Verified the footprint remains stable and explicit:
  `make check` still lists `MLC.infinitely_renormalizable_implies_fast_tower`.

### Remaining Work
- [ ] Replace `infinitely_renormalizable_implies_satellite_data_via_axiom`
  with a non-axiomatic proof (or a strictly weaker/independently justified
  bridge) that yields:
  `∀ c, InfinitelyRenormalizable c → SatelliteRenormalizable c`.
- [ ] Re-run `make check` and confirm
  `MLC.infinitely_renormalizable_implies_fast_tower` disappears.
- [ ] Update README axiom block after the final replacement.

### Current Obstruction
- `InfinitelyRenormalizable` is defined via summability of puzzle moduli,
  while `SatelliteRenormalizable` is defined via fast renormalizability
  iterates on `parameterToBMol`.
- The dictionary from summability/moduli control to fast-tower existence is not
  formalized yet; this is the missing mathematical bridge.

## Execution Steps (Phase 2)
- [x] Step 2.1: Isolate the active target behind a named data wrapper.
- [x] Step 2.2: Route production use-sites through the wrapper.
- [x] Step 2.2b: Decouple tower-building lemmas from IR assumptions by first
  proving satellite-parameter variants.
- [ ] Step 2.3: Implement or import the non-axiomatic bridge theorem.
- [ ] Step 2.4: Remove the axiom declaration from
  `Mlc/FastTowerExistence.lean`.
- [ ] Step 2.5: Run `make check` and `scripts/verify_output.sh`, then sync
  README.

## Completion Checklist
- [x] `make check` does not contain
  `MLC.classify_infinitely_renormalizable`.
- [x] A single named Phase 2 replacement target exists and is used in
  production.
- [ ] `rg -n "^axiom infinitely_renormalizable_implies_fast_tower"` returns no
  matches.
- [ ] `make check` output does not contain
  `MLC.infinitely_renormalizable_implies_fast_tower`.
- [ ] README axiom block matches final `make check` output.

## Outcome So Far
- Phase 1 delivered footprint cleanup and symbol-level elimination.
- Phase 2 now has a single replacement hook and explicit obstruction, so future
  work can target one bridge theorem instead of refactoring core wiring again.
