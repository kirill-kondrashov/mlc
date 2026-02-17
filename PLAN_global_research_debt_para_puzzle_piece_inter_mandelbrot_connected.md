# Plan: Eliminate `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`

## Status (2026-02-17)
- [x] Baseline identified: this axiom is still in the `MLC.mlc_conjecture`
  footprint (`make check`).
- [x] Started isolation refactor in `Mlc/LcAtOfShrink.lean`:
  - `ParaPuzzlePieceInterMandelbrotConnectedData`
  - `para_puzzle_piece_induced_connected_of_data`
  - `lc_at_of_shrink_of_data`
  Existing wrappers still instantiate via
  `para_puzzle_piece_inter_mandelbrot_connected`.
- [ ] Non-axiomatic proof is not yet implemented.

## Scope
- Keep the top-level theorem interface stable:
  `MLC.mlc_conjecture : LocallyConnectedSpace mandelbrotSet`.
- Reduce this debt to a single replacement point
  (`ParaPuzzlePieceInterMandelbrotConnectedData`) before proving it.

## Current Use Surface
- Axiom declaration:
  - `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
- Production dependency path:
  - `Mlc/LcAtOfShrink.lean` (`para_puzzle_piece_induced_connected`)
  - used by `lc_at_of_shrink`, then by main MLC strategy wrappers.
  - data interfaces are in `PuzzleLemmas2`, and default wiring now routes
    through motion-side packaging in `PuzzleBoundaryMotion`.
- [x] Raw-constant uses have been centralized: outside
  `PuzzleLemmas2.lean`, production code now depends on the data hook rather than
  directly on `para_puzzle_piece_inter_mandelbrot_connected`.

## Phase 1: Isolate Replacement Hook
- [x] Add `ParaPuzzlePieceInterMandelbrotConnectedData`.
- [x] Route subtype-connectedness through `_of_data` theorem.
- [x] Route local-connectivity-from-shrink through `_of_data` theorem.
- [x] Add data-parameterized finite/strategy wrappers so production callers can
  be switched without changing top-level signature:
  - `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`
  - `mlc_strategy_of_paraPuzzleConnectedData`
  Existing theorems remain axiom-backed wrappers.
- [x] Add a data-parameterized on-M MLC entry point:
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleConnectedData`
  and keep `mlc_conjecture_of_bottcher_inj_on_basin_onM` as an
  axiom-backed wrapper.
- [x] Extend data-parameterized variants to basin-injectivity and left-inverse
  entry points:
  - `mlc_conjecture_of_bottcher_inj_on_basin_of_paraPuzzleConnectedData`
  - `mlc_conjecture_of_bottcher_left_inverse_on_basin_of_paraPuzzleConnectedData`
  with existing non-suffixed theorems preserved as wrappers.
- [x] Extend data-parameterized variants to uniform and Molecule bridge-target
  entry points:
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_uniformConformalLowerBoundData_of_paraPuzzleConnectedData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_moleculeBridgeTarget_of_paraPuzzleConnectedData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_moleculeUniformBridgeTarget_of_paraPuzzleConnectedData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_of_uniformConformalLowerBoundData_of_paraPuzzleConnectedData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_of_moleculeUniformBridgeTarget_of_paraPuzzleConnectedData`
  with existing non-suffixed theorems preserved as wrappers.
- [x] Centralize axiom-backed instantiation through
  `Quadratic.para_puzzle_transport_witness_hyp`
  (instead of passing the raw axiom constant directly at call sites).
- [x] Narrow the data target to the actually required domain:
  `∀ c ∈ MandelbrotSet, ∀ n, IsConnected (...)`
  (rather than all `c : ℂ`).
- [x] Narrow the remaining axiom statement itself to the on-`M` form
  (`c ∈ MandelbrotSet`) while keeping the same axiom name, so no broader
  dependence remains hidden behind wrappers.

## Phase 2: Implement Non-Axiomatic Theorem
- [ ] Replace the axiom declaration in
  `Mlc/Quadratic/Complex/PuzzleLemmas2.lean` with a theorem.
- [ ] Preferred route:
  prove connectedness of `ParaPuzzlePieceAt c n ∩ MandelbrotSet` via existing
  para-puzzle/Green-sublevel topology lemmas (or an equivalent stronger lemma
  in `ParaPuzzleBasis` that implies this statement).
- [x] Dependency scan (`yoccoz-theorem`, `molecule-conjecture`) did not reveal
  an existing theorem directly proving
  `IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet)`.
  Remaining work is genuinely local to this repository.
- [x] Added explicit stronger bridge decomposition in
  `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`:
  - `ParaPuzzleMandelbrotSubsetData`
  - `para_puzzle_piece_inter_mandelbrot_connected_of_mandelbrot_subset`
  - `para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data`
- [x] Added strategy-level and finitely-renormalizable route variants depending
  on `ParaPuzzleMandelbrotSubsetData` so this stronger bridge can be targeted
  directly while preserving existing APIs.
- [x] Propagated `ParaPuzzleMandelbrotSubsetData` wrappers through the full
  parameterized `MainConjecture` entrypoint family (on-M, basin, uniform,
  molecule-target, and left-inverse routes), keeping legacy wrappers unchanged.
- [x] Added a transport-witness bridge target in
  `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`:
  - `ParaPuzzleInterMandelbrotTransportData`
  - `ParaPuzzleInterMandelbrotTransportExistsData`
  - `para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_data`
  - `para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data`
  - conversion defs:
    `para_puzzle_transport_data_of_connected_data`,
    `para_puzzle_transport_data_of_mandelbrot_subset_data`,
    `para_puzzle_transport_data_of_exists_data`,
    `para_puzzle_transport_exists_data_of_connected_data`,
    `para_puzzle_transport_exists_data_of_transport_data`,
    `para_puzzle_transport_exists_data_of_mandelbrot_subset_data`,
    `para_puzzle_transport_exists_data_of_witness`
  and threaded it through core finite/strategy entrypoints:
  - `lc_at_of_shrink_of_transport_data`
  - `lc_at_of_shrink_of_transport_exists_data`
  - `mlc_finitely_renormalizable_of_paraPuzzleTransportData`
  - `mlc_finitely_renormalizable_of_paraPuzzleTransportExistsData`
  - `mlc_strategy_of_paraPuzzleTransportData`
  - `mlc_strategy_of_paraPuzzleTransportExistsData`
  - `mlc_strategy_of_paraPuzzleMotionWitnessHyp`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleTransportData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleTransportExistsData`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleTransportWitness`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleMotionWitnessHyp`
  so future motion/transport proofs can plug in directly.
- [x] Added motion-side hypothesis packaging in
  `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`:
  - `ParaPuzzleTransportWitnessHyp`
  - `ParaPuzzleTransportWitnessFromBoundaryMotionTarget`
  - `para_puzzle_transport_exists_data_of_motion_witness_hyp`
  - `para_puzzle_transport_witness_hyp_of_transport_exists_data`
  - `para_puzzle_transport_witness_hyp_of_connected_data`
  - `para_puzzle_transport_witness_hyp_of_mandelbrot_subset_data`
  - `para_puzzle_transport_witness_hyp`
  and linked it to the strategy layer via
  `paraPuzzleTransportExistsData_ofMotionWitnessHyp`.
- [x] Re-routed the default on-M wrapper
  `mlc_conjecture_of_bottcher_inj_on_basin_onM` through the
  motion-witness path (`...of_paraPuzzleMotionWitnessHyp`) using the canonical
  default motion witness `para_puzzle_transport_witness_hyp`.
- [x] Canonical axiom-backed connectedness hook now routes through the
  motion-witness layer:
  `para_puzzle_transport_exists_data_of_motion_default` is defined via
  `para_puzzle_transport_exists_data_of_motion_witness_hyp` and
  `para_puzzle_transport_witness_hyp`.
- [x] Raw use of `para_puzzle_piece_inter_mandelbrot_connected` is now isolated
  to a single constructor site:
  `para_puzzle_transport_witness_hyp` in
  `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`.
- [x] Removed unused default axiom-backed constants from
  `Mlc/Quadratic/Complex/PuzzleLemmas2.lean`
  (`para_puzzle_transport_exists_data`, `para_puzzle_connected_data`);
  production wrappers now use motion-sourced transport default
  `Quadratic.para_puzzle_transport_exists_data_of_motion_default`.
- [x] Further rerouted non-suffixed strategy/on-M/basin wrappers through
  motion-witness and on-M routes; `Mlc/MainConjecture.lean` no longer contains
  direct fallback uses of `Quadratic.para_puzzle_connected_data`.
- [x] Lower-level wrappers were likewise rerouted through
  `Quadratic.para_puzzle_transport_exists_data_of_motion_default`; there are
  currently no remaining call sites of `Quadratic.para_puzzle_connected_data`
  or `Quadratic.para_puzzle_transport_exists_data`.
- [x] Added explicit subset-data via-motion routes on non-default paths:
  - `mlc_strategy_of_paraPuzzleMandelbrotSubsetData_via_motionWitnessHyp`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleMandelbrotSubsetData_via_motionWitnessHyp`
  both routed through
  `para_puzzle_transport_witness_hyp_of_mandelbrot_subset_data`.
- [x] Added direct motion-target wrappers in `MainConjecture`:
  - `mlc_strategy_of_paraPuzzleWitnessFromBoundaryMotionTarget`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleWitnessFromBoundaryMotionTarget`
  so the final elimination can be done by proving one target
  (`ParaPuzzleTransportWitnessFromBoundaryMotionTarget`) and swapping default
  wiring.
- [x] Added explicit `..._of_motion` variants for the motion-target route:
  - `mlc_strategy_of_paraPuzzleWitnessFromBoundaryMotionTarget_of_motion`
  - `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_paraPuzzleWitnessFromBoundaryMotionTarget_of_motion`
  to decouple final target replacement from the current default
  `PuzzleBoundaryMotionHyp` constructor path.
- [x] Re-routed `mlc_strategy_of_paraPuzzleMandelbrotSubsetData_via_motionWitnessHyp`
  through the target-level constructor
  `para_puzzle_transport_witness_target_of_witness_hyp`.
- [x] Re-routed default strategy/on-M wrappers through the motion-target hook
  using canonical default `para_puzzle_transport_witness_target`.
- [x] Re-routed default molecule-bridge on-M wrapper through the same
  motion-target hook:
  `mlc_conjecture_of_bottcher_inj_on_basin_onM_of_moleculeBridgeTarget_of_paraPuzzleWitnessFromBoundaryMotionTarget`.
- [x] Re-routed subset-data via-motion wrappers to pass target-level witness
  constructors (`para_puzzle_transport_witness_target_of_witness_hyp`) where
  declaration order permits, reducing intermediate motion-witness routing.
- [x] Strengthened `motion_preserves_para_piece` from a trivial placeholder to
  the local witness shape needed for transport on `M`, and proved:
  - `para_puzzle_transport_witness_hyp_of_boundary_motion`
  - `para_puzzle_transport_witness_from_boundary_motion_target`
  so Step 1 now has a non-axiomatic theorem route from boundary-motion
  hypotheses to the target shape (default constructors remain axiom-backed).
- [x] Factored the remaining raw axiom use into a single named constructor
  theorem:
  - `para_puzzle_transport_witness_hyp_of_axiom`
  so final elimination is now a direct replacement of one theorem body.
- [x] Added direct conversions from motion-target + boundary-motion to
  transport/connected data:
  - `para_puzzle_transport_exists_data_of_boundary_motion_target`
  - `para_puzzle_connected_data_of_boundary_motion_target`
  and routed target+motion strategy through connected-data directly.
- [x] Rerouted later subset-data wrapper families (uniform, molecule-target,
  basin, and left-inverse variants) to consume the motion/on-M subset route
  rather than rebuilding via connected-data at each call site.
- [x] Removed direct subset-to-connected bridge usage in `MainConjecture`:
  subset routes now pass through transport-exists / motion-witness packaging.
- [ ] Prove the on-M replacement data first (minimal needed target), then
  derive any broader wrappers only if still needed.
- [ ] Next concrete proof target: derive
  `ParaPuzzlePieceInterMandelbrotConnectedData` from a non-axiomatic
  parameter-plane transport/motion statement (likely via puzzle boundary motion
  machinery) rather than from a global subset claim.
- [ ] Keep any new assumptions explicit and local; avoid introducing new axioms.

## Phase 3: Rewire and Verify
- [ ] Instantiate `ParaPuzzlePieceInterMandelbrotConnectedData` from the new
  theorem and remove direct axiom reliance from wrappers.
- [ ] Run:
  - `make build`
  - `make check`
  - `scripts/verify_output.sh`
- [ ] Confirm `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
  disappears from `make check` output.
- [ ] Update `README.md` axiom block.

## Completion Checklist
- [ ] `rg -n "^axiom para_puzzle_piece_inter_mandelbrot_connected"` returns no
  matches.
- [ ] `make check` output no longer lists
  `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.
- [ ] `scripts/verify_output.sh` passes with updated README.
