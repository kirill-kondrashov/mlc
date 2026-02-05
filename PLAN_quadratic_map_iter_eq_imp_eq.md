# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Step 1: Build a global inverse branch on the (eventual) slit orbit
- Provide local inverses on the eventual slit orbit via nonvanishing derivative:
  - Prove `EventualSlitNonzeroDeriv c` (nonzero derivative on `eventual_slit_set c ∩ basin`).
  - Use `eventual_slit_inverse_atlas_of_nonzero_deriv` to get `EventualSlitInverseAtlas c`.
- Prove compatibility on overlaps:
  - Establish `EventualSlitInverseCompatible` for the atlas (likely via a local
    uniqueness lemma on overlaps).
- Prove a gluing principle:
  - Establish `EventualSlitInverseGluingWithUniqueness c` (or `EventualSlitInverseGluing c`)
    to obtain `GlobalInverseOnEventualSlit c hA`.

## Step 2: Extend the global inverse from eventual slit orbit to the full basin
- Provide an extension bridge:
  - Prove `EventualSlitGlobalInverseExtensionHyp c` (currently defined as:
    `BasinEventuallyInEventualSlit c ∧ OrbitInverseBranchSystem c`).
  - Use `EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp` to get
    `EventualSlitGlobalInverseExtendsToBasinIter c`.
- Deduce the axiom replacement:
  - Apply `quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_extension` to remove
    `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
