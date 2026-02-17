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
  - hook is now source-localized in `PuzzleLemmas2`:
    `ParaPuzzlePieceInterMandelbrotConnectedData` and
    `para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom`.

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
- [x] Centralize axiom-backed instantiation through
  `Quadratic.para_puzzle_piece_inter_mandelbrot_connected_data_of_axiom`
  (instead of passing the raw axiom constant directly at call sites).
- [x] Narrow the data target to the actually required domain:
  `∀ c ∈ MandelbrotSet, ∀ n, IsConnected (...)`
  (rather than all `c : ℂ`).

## Phase 2: Implement Non-Axiomatic Theorem
- [ ] Replace the axiom declaration in
  `Mlc/Quadratic/Complex/PuzzleLemmas2.lean` with a theorem.
- [ ] Preferred route:
  prove connectedness of `ParaPuzzlePieceAt c n ∩ MandelbrotSet` via existing
  para-puzzle/Green-sublevel topology lemmas (or an equivalent stronger lemma
  in `ParaPuzzleBasis` that implies this statement).
- [ ] Prove the on-M replacement data first (minimal needed target), then
  derive any broader wrappers only if still needed.
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
