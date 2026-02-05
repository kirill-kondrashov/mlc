# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Step 1: Build a global inverse branch on the (eventual) slit orbit
- [ ] Provide local inverses on the eventual slit orbit via nonvanishing derivative:
  - [x] Prove `EventualSlitNonzeroDeriv c` from hypotheses
    (`EventualSlitOpenNeighborhood` + `EventualSlitDerivNonzero`).
  - [x] Use `eventual_slit_inverse_atlas_of_nonzero_deriv` to get `EventualSlitInverseAtlas c`.
- [ ] Prove compatibility on overlaps:
  - [x] Establish `EventualSlitInverseCompatible` from hypotheses
    (`EventualSlitLocalUniqueness` + `EventualSlitOverlapHyp` + `EventualSlitCompatibilityFromOverlap`).
- [x] Prove a gluing principle:
  - [x] Establish `EventualSlitInverseGluingWithUniqueness c` (or `EventualSlitInverseGluing c`)
    to obtain `GlobalInverseOnEventualSlit c hA`.

## Step 2: Extend the global inverse from eventual slit orbit to the full basin
- [ ] Provide an extension bridge:
  - [x] Prove `BasinEventuallyInEventualSlit c`.
  - [x] Reduce `OrbitInverseBranchSystem c` to a single left inverse for `quadratic_map c`
    (`orbit_inverse_branch_system_of_left_inverse`).
  - [ ] Provide `OrbitInverseBranchSystem c`.
  - [ ] Combine into `EventualSlitGlobalInverseExtensionHyp c`
    (currently defined as `BasinEventuallyInEventualSlit c ∧ OrbitInverseBranchSystem c`).
  - [x] Use `EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp` to get
    `EventualSlitGlobalInverseExtendsToBasinIter c`.
- [x] Deduce the axiom replacement (once Step 2 bridge exists):
  - [x] Apply `quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_extension` (or
    `..._hyp`) to remove `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
