# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Step 1: Build a global inverse branch on the (eventual) slit orbit
- Provide local inverses on the eventual slit orbit via nonvanishing derivative:
  - Prove `EventualSlitNonzeroDeriv c` (nonzero derivative on `eventual_slit_set c ∩ basin`).
  - Use `local_inverse_at_of_eventual_slit` to get `EventualSlitInverseAtlas c`.
- Prove compatibility on overlaps:
  - Establish `EventualSlitInverseCompatible` for the atlas.
- Prove a gluing principle:
  - Establish `EventualSlitInverseGluing c` to obtain `GlobalInverseOnEventualSlit c hA`.

## Step 2: Extend the global inverse from eventual slit orbit to the full basin
- Provide an extension bridge:
  - Prove `EventualSlitGlobalInverseExtendsToBasin c hA hG`.
  - Use `quadratic_map_left_inverse_on_basin_of_global_inverse` to get a left inverse
    of `quadratic_map` on `basin_of_infinity`.
- Deduce the axiom replacement:
  - Apply `quadratic_map_iter_eq_imp_eq_of_iter_left_inverse` to remove
    `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
