# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Status (2026-02-16)
- [x] Eliminated from the `MLC.mlc_conjecture` axiom footprint.
- [x] `make check` no longer lists `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [x] No production use-site remains in `Mlc/MainConjecture.lean`.
- [x] `MLC.bottcher_map_inj_on_K` is no longer in the axiom footprint of
  `MLC.mlc_conjecture`; the bridge now routes via
  `bottcher_map_inj_on_basin_onM_via_basin_dynamics`.
- [x] `MLC.Quadratic.bottcher_seq_converges` is no longer in the axiom
  footprint of `MLC.mlc_conjecture`.

## What Is Already Done
- [x] Main theorem wiring is parameterized:
  - `mlc_conjecture_of_bottcher_inj_on_basin`
  - `mlc_conjecture_of_bottcher_left_inverse_on_basin`
  - `mlc_conjecture_of_bottcher_isLocalHomeomorph`
  - `mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin`
  - `mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin_data`
  - `mlc_conjecture_of_bottcher_proper_deriv_ne_zero_mem_nhds_slit`
  - `mlc_conjecture_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit`
  - `mlc_conjecture_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_data`
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
- [x] `mlc_conjecture` now instantiates the on-M basin-injectivity wrapper
  (`mlc_conjecture_of_bottcher_map_inj_on_basin_onM_data`), and the old
  `quadratic_map_iter_eq_imp_eq` bridge has been removed from this path.
- [x] Step 2b bridge is now explicitly factored and wired constructively:
  - `BottcherMapInjOnBasinOnMData`
  - `bottcher_map_inj_on_basin_onM_via_basin_dynamics`
  - `bottcher_map_inj_on_basin_onM_target`
  This route no longer uses contradiction (`False.elim`) and does not reintroduce
  `quadratic_map_iter_eq_imp_eq`.
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
  - `mlc_conjecture_of_basin_bottcher_pointwise_left_inverse_data_onM`
  - `mlc_conjecture_of_bottcher_map_inj_on_basin_onM_data`
  - `basin_bottcher_pointwise_left_inverse_data_onM_of_global`
  - `BottcherMapInjOnBasinOnMData`
  - `bottcher_map_inj_on_basin_onM_via_basin_dynamics`
  - `bottcher_map_inj_on_basin_onM_target`
  - `basin_bottcher_pointwise_left_inverse_data_onM_of_bottcher_map_inj_on_basin_onM`
  - `bottcher_map_inj_on_basin_onM_data_of_basin_bottcher_pointwise_left_inverse_data_onM`
  - `BottcherIsLocalHomeomorphOnMData`
  - `bottcher_map_inj_on_basin_onM_data_of_bottcher_isLocalHomeomorph_onM_data`
  - `mlc_conjecture_of_bottcher_isLocalHomeomorph_onM_data`
  - `basin_bottcher_pointwise_left_inverse_data_iff_bottcher_map_inj_on_basin`
  - `basin_bottcher_pointwise_left_inverse_data_onM_iff_bottcher_map_inj_on_basin_onM`
  - `basin_bottcher_pointwise_left_inverse_data_onM_iff_bottcher_map_inj_on_basin_onM_data`
  - `external_ray_map_left_inverse_on_basin_of_bottcher_map_inj_on_basin`
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
- [x] Added topology prelims for a future non-axiomatic basin-injectivity route
  (currently in `BottcherOutsidePlan`):
  - `isDiscrete_fiber_of_isLocallyInjective`
  - `finite_fiber_of_isProperMap_isLocallyInjective`
  - `isDiscrete_fiber_of_isLocalHomeomorphOn_of_fiber_subset`
  - `finite_fiber_of_isProperMap_isLocalHomeomorphOn_of_fiber_subset`
  - `range_isOpen_of_isLocalHomeomorph`
  - `range_isClosed_of_isProperMap`
  - `range_eq_univ_of_isProperMap_isLocalHomeomorph`
  - `exists_open_preimage_subset_of_closedMap_of_fiber_subset`
  - `exists_pairwise_disjoint_ball_of_finite`
  - `exists_open_preimage_subset_iUnion_ball_of_finite_fiber`
  - `exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber`
  - `exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber_on`
  - `exists_open_preimage_subset_iUnion_disjoint_inj_subset_of_finite_fiber_on`
  - `exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj`
  - `finite_fiber_of_mem_open_of_preimage_subset_iUnion_inj`
  - `natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj`
  - `exists_open_finite_fiber_of_closedMap_localHomeomorph_of_finite_fiber`
  - `exists_open_natCard_fiber_le_of_closedMap_localHomeomorph_of_finite_fiber`
  - `exists_open_natCard_fiber_le_of_closedMap_localHomeomorphOn_of_finite_fiber_subset`
  - `isOpen_image_of_isLocalHomeomorphOn_aux`
  - `exists_injective_fiber_map_of_mem_iInter_image_of_pairwise_disjoint`
  - `natCard_fiber_eq_of_mem_open_of_preimage_subset_iUnion_disjoint_inj_and_mem_iInter_image`
  - `exists_open_natCard_fiber_eq_of_closedMap_localHomeomorph_of_finite_fiber`
  - `exists_open_natCard_fiber_eq_of_closedMap_localHomeomorphOn_of_open_of_finite_fiber_subset`
  - `natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorph`
  - `natCard_fiber_eq_of_isProperMap_isLocalHomeomorph`
  - `natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset`
  - `natCard_fiber_eq_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset`
  - `injective_of_isProperMap_isLocalHomeomorph_of_exists_natCard_fiber_eq_one`
  - `injective_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset_of_exists_natCard_fiber_eq_one`
  - `natCard_fiber_isLocallyConstant_on_image_of_isProperMap_isLocalHomeomorphOn_of_open`
  - `natCard_fiber_eq_on_image_of_isProperMap_isLocalHomeomorphOn_of_open_of_connected_image`
  - `injOn_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset_on_image_of_connected_image`
  - `natCard_fiber_eq_one_of_existsUnique`
  - `natCard_fiber_eq_one_of_injOn_of_mem_image_of_fiber_subset`
  - `injective_of_isProperMap_isLocalHomeomorph_of_injOn_of_mem_image_of_fiber_subset`
  - `bottcher_map_injective_of_proper_localHomeomorph_and_outside_seed`
  - `bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed`
  - `bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed'`
  - `exists_bottcher_outside_seed_of_continuous`
  - `bottcher_map_inj_on_basin_of_proper_localHomeomorph`
  - `bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin`
  - `bottcher_map_inj_on_basin_of_isLocalHomeomorph`
  - `basin_bottcher_pointwise_left_inverse_data_of_bottcher_isLocalHomeomorph`
  - `basin_bottcher_pointwise_left_inverse_data_of_bottcher_proper_localHomeomorphOn_basin`
  - `basin_bottcher_pointwise_left_inverse_data_of_bottcher_proper_localHomeomorphOn_basin_data`
  - `basin_bottcher_pointwise_left_inverse_data_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit`
  - `bottcher_proper_localHomeomorphOn_basin_data_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit`
  - `not_bottcher_proper_localHomeomorphOn_basin_data`
  - `not_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_data`
  - `not_bottcher_isLocalHomeomorph_data`
  - `exists_open_subset_slit_orbit_basin_of_mem_nhds`
  - `bottcher_map_analyticAt_of_mem_nhds_slit_basin`
  - `bottcher_map_local_inj_of_deriv_ne_zero_of_mem_nhds_slit_basin`
  - `bottcher_map_isLocalHomeomorphOn_basin_of_deriv_ne_zero_of_mem_nhds_slit`
  - `bottcher_map_re_neg_of_pos_real`
  - `bottcher_map_not_continuousAt_zero`
  - `bottcher_map_not_continuous`
  - `bottcher_map_not_isProperMap`

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
- [x] Proper/local-homeomorphism Step 2b redesign data is inconsistent with the
  current `bottcher_map` model:
  - `bottcher_map_not_continuousAt_zero`
  - `bottcher_map_not_continuous`
  - `bottcher_map_not_isProperMap`
  - `not_bottcher_proper_localHomeomorphOn_basin_data`
  - `not_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_data`
  - `not_bottcher_proper_localHomeomorphOn_basin_onM_data`
  - `not_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_onM_data`.
  So the proper/local-homeomorphism data route cannot be the final non-axiomatic
  replacement target under current definitions.
- [x] The global and on-M local-homeomorphism routes are also inconsistent:
  - `not_bottcher_isLocalHomeomorph_data`
  - `not_bottcher_isLocalHomeomorph_onM_data`.
- [x] The `bottcher_map_inj_on_K` route is inconsistent with the current model:
  - `not_bottcher_map_inj_on_K_zero`.
  - `not_bottcher_map_inj_on_K_data`.
  - `false_of_bottcher_map_inj_on_K_axiom`.
- [x] Added concrete non-Mandelbrot escape/fixed-point witnesses for follow-up
  bridge work:
  - `zero_mem_basin_two`
  - `zero_not_mem_K_two`
  - `fixed_point_two_ne_zero`.
- [x] Removed the temporary `bottcher_map_inj_on_K` contradiction dependency from
  the production MLC bridge by replacing it with an external-ray contradiction:
  - `bottcher_map_continuousAt_of_ne_zero`
  - `ofReal_mem_basin_two`
  - `ofReal_not_mem_K_two`
  - `bottcher_map_eq_one_not_mem_K_two`
  - `bottcher_map_fixed_point_two_ne_one`
  - `false_of_external_ray_axioms`.
- [x] Refined the contradiction witness to remove `extended_ray_map_continuous`
  from that local bridge:
  - `log_norm_le_green_add_escape_const_of_norm_gt_escape_bound`
  - `false_of_external_ray_axioms` now uses a bounded-subsequence/Green-limit
    argument and depends only on `external_ray_map_exists`.
- [x] Added on-M Step 2b data wrappers and obstruction lemmas:
  - `BottcherProperLocalHomeomorphOnBasinOnMData`
  - `BottcherContinuousDerivNeZeroMemNhdsSlitOnMData`
  - `mlc_conjecture_of_bottcher_proper_localHomeomorphOn_basin_onM_data`
  - `mlc_conjecture_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_onM_data`
  - `BottcherIsLocalHomeomorphOnMData`
  - `mlc_conjecture_of_bottcher_isLocalHomeomorph_onM_data`
  - `bottcher_map_inj_on_basin_onM_data_of_bottcher_proper_localHomeomorphOn_basin_onM_data`
  - `bottcher_map_inj_on_basin_onM_data_of_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_onM_data`
  - `bottcher_map_inj_on_basin_onM_data_of_bottcher_isLocalHomeomorph_onM_data`
  - `zero_mem_mandelbrotSet`
  - `not_bottcher_proper_localHomeomorphOn_basin_onM_data`
  - `not_bottcher_continuous_deriv_ne_zero_mem_nhds_slit_onM_data`
  - `not_bottcher_isLocalHomeomorph_onM_data`
- [x] Added direct on-M injectivity preliminaries for the remaining Step 2b
  target:
  - `bottcher_map_eq_imp_green_eq`
  - `zero_not_mem_basin_of_mem_mandelbrot`
  - `ne_zero_of_mem_basin_of_mem_mandelbrot`
  - `bottcher_map_ne_of_neg_of_ne_zero`
  - `eq_of_bottcher_eq_and_quadratic_eq_of_mem_mandelbrot`
  - `eq_of_iterate_eq_and_bottcher_eq_on_basin_onM`
  - `exists_iter_eq_of_bottcher_eq_on_basin_via_outside`
  - `bottcher_map_inj_on_basin_of_mem_mandelbrot`

## Remaining Work
- [x] Reformulate the elimination target: `quadratic_map_iter_eq_imp_eq` has been
  removed from the `mlc_conjecture` footprint.
- [x] Identify and prove the minimal *true* replacement needed in the main path
  (`Mlc/MainConjecture.lean`) so the bridge does not rely on deriving `False`
  from external-ray axioms.
- [x] Replaced
  `bottcher_map_inj_on_basin_onM_via_external_ray_axioms`
  with a constructive on-M basin-injectivity route:
  - `bottcher_map_ne_of_neg_of_ne_zero`
  - `eq_of_bottcher_eq_and_quadratic_eq_of_mem_mandelbrot`
  - `eq_of_iterate_eq_and_bottcher_eq_on_basin_onM`
  - `exists_iter_eq_of_bottcher_eq_on_basin_via_outside`
  - `bottcher_map_inj_on_basin_of_mem_mandelbrot`
  - `bottcher_map_inj_on_basin_onM_via_basin_dynamics`

## Execution Steps
- [x] Step 1: Refactor the bottcher-injectivity chain so it does not depend on
  `quadratic_map_iter_eq_imp_eq` directly.
- [x] Step 2a: Replace the wrapper instantiation with the basin-injectivity route.
- [x] Step 2b: Replace the remaining axiom-backed construction of basin injectivity
  (formerly `bottcher_map_inj_on_basin_onM_via_external_ray_axioms`)
  with a constructive proof (`bottcher_map_inj_on_basin_onM_via_basin_dynamics`).
- [x] Step 3: Run `make check` and confirm `MLC.Quadratic.quadratic_map_iter_eq_imp_eq` disappears.
- [x] Step 4: Run `scripts/verify_output.sh` and update README axiom section to match final output.

## Completion Checklist
- [x] `rg -n "Quadratic\\.quadratic_map_iter_eq_imp_eq\\b" Mlc` has no production use-site in main MLC path.
- [x] `make check` no longer reports `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [x] README axiom block is synchronized with final `make check` output.
