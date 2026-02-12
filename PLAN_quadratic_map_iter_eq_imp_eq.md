# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Status (2026-02-12)
- [x] Goal achieved for current MLC assembly:
  `check_axioms` no longer lists `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [x] `scripts/verify_output.sh` passes after updating the README expected-output block.

## Completed work
- [x] Added the eventual-slit extension scaffolding and helper interfaces in
  `Mlc/Quadratic/Complex/Bottcher/InverseBranchSlitUse.lean`.
- [x] Refactored basin/global injectivity APIs to take a derived iterate-equality implication
  hypothesis (`h_iter_eq_imp`) rather than calling the axiom internally:
  - `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`
- [x] Added iter-left-inverse specializations:
  - `bottcher_map_inj_theorem_of_iter_left_inverse`
  - `bottcher_map_inj_on_outside_of_slit_of_iter_left_inverse`
- [x] Updated `Mlc/MainConjecture.lean` wiring so the axiom is no longer part of the
  `mlc_conjecture` dependency output.
- [x] Fixed pending proof errors in `BottcherOutsidePlan.lean` needed to compile this route.

## Remaining research/debt (deferred)
- [ ] Prove a concrete global extension bridge:
  `EventualSlitGlobalInverseExtensionBridge c hA hG` from actual dynamics.
- [ ] Derive `EventualSlitGlobalInverseExtensionHyp c` from concrete extension data and obtain
  `EventualSlitGlobalInverseExtendsToBasinIter c` without fallback assumptions.
- [ ] Complete the stronger global properness/degree-one route to injectivity on full basin
  with fully canonical hypotheses.
