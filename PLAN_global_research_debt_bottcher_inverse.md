# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Status (2026-02-13)
- [ ] Not eliminated yet.
- [ ] `make check` still lists `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [ ] Only remaining production use-site:
  `Mlc/MainConjecture.lean:148`
  (isolated behind `bottcher_map_inj_on_basin_via_iter_eq_axiom`).
- [x] `MLC.bottcher_map_inj_on_K` is no longer in the axiom footprint of
  `MLC.mlc_conjecture` after the basin-injectivity refactor.
- [x] `MLC.Quadratic.bottcher_seq_converges` is no longer in the axiom
  footprint of `MLC.mlc_conjecture`.

## What Is Already Done
- [x] Main theorem wiring is parameterized:
  - `mlc_conjecture_of_bottcher_inj_on_basin`
  - `mlc_conjecture_of_bottcher_left_inverse_on_basin`
  - `mlc_conjecture_of_iter_eq_imp`
  - `mlc_conjecture_of_iter_eq_imp_via_pullback_root`
  - `mlc_conjecture_of_quadratic_left_inverse`
  - `mlc_conjecture_of_pullback_root`
  - `mlc_conjecture_of_eventual_slit_global_extension`
- [x] Minimal bridge formalized:
  - `bottcher_map_inj_on_basin_of_left_inverse`
  - basin left-inverse identity for `external_ray_map ∘ bottcher_map` now
    explicitly implies basin injectivity.
- [x] Böttcher injectivity chain was refactored:
  - core theorem now takes basin injectivity directly:
    `bottcher_map_inj_theorem_of_inj_basin`
  - iterate-equality is now only a wrapper route into basin injectivity:
    `bottcher_map_inj_theorem`.
- [x] `mlc_conjecture_of_pullback_root` no longer routes through
  iterate-equality; it now closes through
  `mlc_conjecture_of_bottcher_left_inverse_on_basin`.
- [x] `mlc_conjecture` now instantiates the basin-injectivity route directly
  (`mlc_conjecture_of_bottcher_inj_on_basin`), so the remaining axiom use is
  isolated to `bottcher_map_inj_on_basin_via_iter_eq_axiom` in
  `Mlc/MainConjecture.lean:144`.
- [x] Remaining axiom bridge is now explicitly factored:
  - `bottcher_map_inj_on_basin_via_iter_eq_axiom`
  This is the single replacement target for Step 2b.
- [x] Added non-axiomatic eventual-slit global-inverse injectivity route:
  - `bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_pointwise`
  - `EventualSlitGlobalInverseData`
  - `EventualSlitPointwiseLeftInverseData`
  - `BasinBottcherPointwiseLeftInverseData`
  - `eventual_slit_pointwise_left_inverse_data_of_eventual_slit_global_inverse_data`
  - `basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_pointwise_left_inverse_data`
  - `eventual_slit_pointwise_left_inverse_data_of_basin_bottcher_pointwise_left_inverse_data`
  - `bottcher_map_inj_on_basin_of_eventual_slit_pointwise_left_inverse_data`
  - `bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data`
  - `mlc_conjecture_of_eventual_slit_pointwise_left_inverse_data`
  - `mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data`
  - `basin_bottcher_pointwise_left_inverse_data_iff_bottcher_map_inj_on_basin`
  - `bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_data`
  - `mlc_conjecture_of_eventual_slit_global_inverse_data`
  - `mlc_conjecture_of_eventual_slit_global_inverse`
  - `mlc_conjecture_of_eventual_slit_inverse_gluing`
  - `mlc_conjecture_of_eventual_slit_local_to_global`
  - `EventualSlitNonzeroDerivCompatibleGluingData`
  - `eventual_slit_global_inverse_data_of_nonzero_deriv_compatible_gluing_data`
  - `mlc_conjecture_of_eventual_slit_nonzero_deriv_compatible_gluing`
  - `mlc_conjecture_of_eventual_slit_global_extension` now uses basin-injectivity
    directly through that route.
- [x] Green-sublevel connectivity path is now basin-injectivity-native:
  - `green_sublevel_joined_to_Kc` uses
    `Set.InjOn (bottcher_map c) (basin_of_infinity c)` (not global injectivity).
  - `green_sublevel_connected` now takes basin injectivity directly.
  - `mlc_conjecture_of_bottcher_inj_on_basin` passes `h_inj_basin` directly,
    removing the prior `bottcher_map_inj_theorem_of_inj_basin` bridge from this path.
- [x] Reduction chain from a basin left inverse of `quadratic_map` to iterate-equality implication is formalized.
- [x] Pullback-root formulation is formalized (`BasinQuadraticPullbackRoot` and consequences).
- [x] `mlc_conjecture` itself remains unchanged in signature (no extra hypotheses).
- [x] No new axioms were introduced in this line of work.
- [x] Viability check for the left-inverse target is now formalized:
  - `quadratic_map_not_injOn_basin`
  - `not_quadratic_map_left_inverse_on_basin`
  This shows `quadratic_map` is not injective on `basin_of_infinity c`, so a
  global basin left inverse cannot exist.
- [x] Direct obstruction for the current iterate-equality axiom shape:
  - `not_quadratic_map_iter_eq_imp_eq`
  The current proposition implies injectivity of `quadratic_map` on the basin,
  so it is not a viable “true replacement target” under present definitions.
- [x] Local-to-global eventual-slit package with explicit overlap hypothesis is
  inconsistent:
  - `not_eventual_slit_overlap_hyp_data`
  - `not_eventual_slit_local_to_global_data`
  So the overlap-based route is not a viable Step 2b replacement target under
  current definitions.
- [x] Inconsistent hook routes are now discharged directly by contradiction
  (without routing through `quadratic_map_iter_eq_imp_eq_*` bridge lemmas):
  - `mlc_conjecture_of_iter_eq_imp`
  - `mlc_conjecture_of_iter_eq_imp_via_pullback_root`
  - `mlc_conjecture_of_quadratic_left_inverse`
  - `mlc_conjecture_of_basin_sqrt_branch_of_injective`
  - `mlc_conjecture_of_basin_sqrt_branch`
  - `mlc_conjecture_of_eventual_slit_global_bridge`

## Ruled-Out Routes (Formal Obstructions)
- [x] Escape-time candidate route is inconsistent:
  - `not_EventualSlitEscapeIterateLeftInverse`.
- [x] Current bridge predicate is inconsistent:
  - `not_EventualSlitGlobalInverseExtensionBridge`
  - `not_eventual_slit_global_bridge_data`.
- [x] Eventual-slit global-inverse data is inconsistent:
  - `eventual_slit_subset_slit_orbit_of_inverse_atlas`
  - `not_EventualSlitInverseAtlas_zero`
  - `not_eventual_slit_global_inverse_data`.
  Consequently, the direct global-inverse replacement target
  (`EventualSlitGlobalInverseData`) is not viable under current definitions.
- [x] Overlap-free decomposed eventual-slit data is also inconsistent:
  - `not_eventual_slit_nonzero_deriv_compatible_gluing_data`.
  This route implies `EventualSlitGlobalInverseData`, which is already ruled out.
- [x] Eventual-slit extension-to-basin data is inconsistent:
  - `not_eventual_slit_global_extension_data`.
  This route is equivalent to a basin-wide left inverse of `quadratic_map`.
- [x] Global fixed-slit and rotated-slit branch assumptions are inconsistent.
- [x] Global single-`sqrt` basin branch assumption is inconsistent.
- [x] Basin-wide left-inverse target is inconsistent with current dynamics model:
  - `quadratic_map_not_injOn_basin`
  - `not_quadratic_map_left_inverse_on_basin`.

## Remaining Work (Single Real Blocker)
- [ ] Reformulate the elimination target: the previous “prove a basin left inverse”
  route is impossible, so `quadratic_map_iter_eq_imp_eq` cannot be replaced by that
  statement.
- [ ] Identify and prove the minimal *true* replacement needed in the main path
  (`Mlc/MainConjecture.lean`), likely by avoiding any requirement equivalent to
  injectivity of `quadratic_map` on the whole basin.
- [ ] Concretely, replace `bottcher_map_inj_on_basin_via_iter_eq_axiom` by proving
  one non-axiomatic basin-injectivity route. Atlas/global-inverse/gluing
  eventual-slit candidates are blocked by formal obstructions. Current open redesign target:
  - `BasinBottcherPointwiseLeftInverseData`
  (equivalent to `EventualSlitPointwiseLeftInverseData` via
  `basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_pointwise_left_inverse_data` and
  `eventual_slit_pointwise_left_inverse_data_of_basin_bottcher_pointwise_left_inverse_data`,
  and equivalent to basin injectivity via
  `basin_bottcher_pointwise_left_inverse_data_iff_bottcher_map_inj_on_basin`).
  This is now wired to MLC via
  `mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data` and remains the
  next candidate to realize without new axioms or new hypotheses in
  `mlc_conjecture`.

## Execution Steps Left
- [x] Step 1: Refactor the bottcher-injectivity chain so it does not depend on
  `quadratic_map_iter_eq_imp_eq` directly.
- [x] Step 2a: Replace the wrapper instantiation with the basin-injectivity route.
- [ ] Step 2b: Replace the remaining axiom-backed construction of basin injectivity
  (currently `bottcher_map_inj_on_basin_via_iter_eq_axiom`)
  with a non-axiomatic proof.
- [ ] Step 3: Run `make check` and confirm `MLC.Quadratic.quadratic_map_iter_eq_imp_eq` disappears.
- [ ] Step 4: Run `scripts/verify_output.sh` and update README axiom section to match final output.

## Completion Checklist
- [ ] `rg -n "Quadratic\\.quadratic_map_iter_eq_imp_eq\\b" Mlc` has no production use-site in main MLC path.
- [ ] `make check` no longer reports `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [ ] README axiom block is synchronized with final `make check` output.
