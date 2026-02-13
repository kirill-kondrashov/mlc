# Plan: Eliminate `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`

## Status (2026-02-12)
- [ ] Not fully eliminated yet.
- [ ] `make check` still lists `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [ ] Current explicit use-site in the MLC pipeline:
  `Mlc/MainConjecture.lean` (wrapper call at line 195).

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
- [x] Updated `Mlc/MainConjecture.lean` wiring so iterate-equality implications can be threaded
  explicitly through intermediate theorems.
- [x] Fixed pending proof errors in `BottcherOutsidePlan.lean` needed to compile this route.
- [x] Added direct reduction chain from a proved bridge to the final target:
  - `EventualSlitGlobalInverseExtensionHyp_of_bridge`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_bridge`
  - `quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_bridge`
- [x] Added an explicit escape-time candidate construction and bridge reducer:
  - `eventualSlitEscapeTime`, `eventualSlitEscapeTime_spec`
  - `eventual_slit_orbit_of_iter_eventual`
  - `basin_subset_eventual_slit_set`
  - `eventualSlitBridgeCandidate`
  - `eventualSlitBridgeCandidate_eq_escape_iterate`
  - `eventualSlitBridgeCandidate_mem_basin`
  - `eventualSlitBridgeCandidate_repr`
  - `bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_global_inverse`
  - `EventualSlitBridgeCandidateLeftInverse`
  - `EventualSlitEscapeIterateLeftInverse`
  - `EventualSlitBridgeCandidateLeftInverse_iff_escape_iterate`
  - `EventualSlitGlobalInverseExtensionBridge_of_candidate_left_inverse`
  - `EventualSlitGlobalInverseExtensionBridge_of_escape_iterate`
  - `iterate_mul_eq_self_of_iterate_eq_self`
  - `not_mem_basin_of_periodic`
  - `not_EventualSlitEscapeIterateLeftInverse`
- [x] Added a concrete alternative reduction chain via basin left inverses / sqrt branches:
  - `EventualSlitGlobalInverseExtensionHyp_of_left_inverse`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_left_inverse`
  - `quadratic_map_iter_eq_imp_eq_of_left_inverse`
  - `quadratic_map_iter_eq_imp_eq_of_sqrt_branch_slitPlaneRight`
  - `quadratic_map_iter_eq_imp_eq_of_sqrt_branch_slitPlaneRotRight`
  - `EventualSlitGlobalInverseExtendsToBasin_of_left_inverse`
  - `EventualSlitGlobalInverseExtensionHyp_of_sqrt_branch_slitPlaneRight`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_sqrt_branch_slitPlaneRight`
  - `EventualSlitGlobalInverseExtendsToBasin_of_sqrt_branch_slitPlaneRight`
  - `EventualSlitGlobalInverseExtensionHyp_of_sqrt_branch_slitPlaneRotRight`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_sqrt_branch_slitPlaneRotRight`
  - `EventualSlitGlobalInverseExtendsToBasin_of_sqrt_branch_slitPlaneRotRight`
- [x] Added a variable-branch (image-of-basin) interface that avoids fixed global slit-membership:
  - `BasinBottcherSquareRootRightInverse`
  - `quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch`
  - `EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_basin_sqrt_branch`
  - `quadratic_map_iter_eq_imp_eq_of_basin_sqrt_branch`
- [x] Reduced variable-branch side conditions further using global Böttcher injectivity:
  - `bottcher_left_inverse_on_basin_of_injective`
  - `EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch_of_injective`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_basin_sqrt_branch_of_injective`
  - `quadratic_map_iter_eq_imp_eq_of_basin_sqrt_branch_of_injective`
- [x] Refactored main theorem wiring to isolate the iterate-equality input:
  - Added `mlc_conjecture_of_iter_eq_imp` in `Mlc/MainConjecture.lean`.
  - `mlc_conjecture` is now a thin wrapper instantiating that parameterized theorem.
- [x] Added a concrete top-level hook for the variable-branch replacement route:
  - `mlc_conjecture_of_basin_sqrt_branch_of_injective` in `Mlc/MainConjecture.lean`,
    reducing MLC to `quadratic_map_iter_eq_imp_eq_of_basin_sqrt_branch_of_injective`
    once per-parameter branch data is supplied.
- [x] Added a weaker top-level hook using direct basin left-inverse input
  (avoids requiring global injectivity as a separate hypothesis):
  - `mlc_conjecture_of_basin_sqrt_branch` in `Mlc/MainConjecture.lean`.
- [x] Added a pullback-root replacement interface (non-vacuous shape):
  - `BasinQuadraticPullbackRoot`
  - `quadratic_map_left_inverse_on_basin_of_pullback_root`
  - `EventualSlitGlobalInverseExtensionHyp_of_pullback_root`
  - `EventualSlitGlobalInverseExtendsToBasinIter_of_pullback_root`
  - `quadratic_map_iter_eq_imp_eq_of_pullback_root`
  - `exists_BasinQuadraticPullbackRoot_of_left_inverse`
  - `bottcher_left_inverse_on_basin_of_quadratic_left_inverse`
  - `exists_pullback_root_data_of_left_inverse`
  - `exists_pullback_root_data_of_global_inverse_extension`
  - top-level hook `mlc_conjecture_of_pullback_root` in `Mlc/MainConjecture.lean`
- [x] Added internal reductions from iterate-equality implication to left-inverse data:
  - generic `hasLeftInverseOn_of_injOn` in `Mlc/Quadratic/Complex/InverseBranch.lean`
  - `quadratic_map_left_inverse_on_basin_of_iter_eq_imp`
  - `exists_pullback_root_data_of_iter_eq_imp`
  - top-level bridge `mlc_conjecture_of_iter_eq_imp_via_pullback_root`
    in `Mlc/MainConjecture.lean`
  These are scaffolding lemmas only; `mlc_conjecture` still keeps its original
  signature and current axiom footprint (no additional axioms introduced there).
- [x] Added direct top-level bridge hooks from eventual-slit bridge data:
  - `exists_pullback_root_data_of_bridge`
  - `mlc_conjecture_of_eventual_slit_global_bridge`
  This isolates the remaining work to constructing bridge data, without touching
  `mlc_conjecture`.
- [x] Added a formal obstruction for one naive sqrt-branch side condition:
  - `not_bottcher_map_mem_slitPlaneRight_on_basin`
  - `no_sqrt_branch_slitPlaneRight_data_on_full_basin`
  - `not_bottcher_map_mem_slitPlaneRotRight_on_basin`
  - `no_sqrt_branch_slitPlaneRotRight_data_on_full_basin`
  This shows the global assumption
  `∀ z ∈ basin_of_infinity c, bottcher_map c z ∈ slitPlaneRight`
  is inconsistent with `bottcher_map_surj`, so the full-basin
  single-slit route (`slitPlaneRight` or any fixed rotated `slitPlaneRotRight θ`)
  is not viable as stated.
- [x] Added a formal obstruction for the global variable-branch `sqrt` interface:
  - `no_BasinBottcherSquareRootRightInverse`
  - `no_basin_sqrt_branch_data_on_full_basin`
  So a single global `sqrt : ℂ → ℂ` satisfying
  `BasinBottcherSquareRootRightInverse c sqrt` is inconsistent with
  `bottcher_map_surj` (witnessed by `2` and `-2`), and must be replaced by
  orbit-dependent/local pullback data.

## Remaining research/debt (blocking elimination)
- [ ] Step 1: Prove a concrete global extension bridge:
  `EventualSlitGlobalInverseExtensionBridge c hA hG` from actual dynamics.
  Current reduced target from the escape-time candidate route
  (`EventualSlitBridgeCandidateLeftInverse` / `EventualSlitEscapeIterateLeftInverse`)
  is now formally shown inconsistent with basin dynamics
  (`not_EventualSlitEscapeIterateLeftInverse`).
  So this route is blocked. We now have a replacement reduction through
  `HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c)`
  and explicit sqrt-branch interfaces on slit domains, but the concrete dynamic
  construction of those hypotheses is still open.
  Also, the naive full-basin single-slit membership side conditions have been
  formally ruled out (both fixed and rotated slit halves), so Step 1 must use
  genuinely local/variable branch data or a different pullback/gluing mechanism.
- [ ] Step 2: Derive `EventualSlitGlobalInverseExtensionHyp c` from concrete extension data and obtain
  `EventualSlitGlobalInverseExtendsToBasinIter c` without fallback assumptions.
  This reduction is formalized (`..._of_left_inverse`, `..._of_sqrt_branch_*`);
  remaining work is to discharge the pullback-root side conditions
  (`BasinQuadraticPullbackRoot`, basin `MapsTo` for the pullback map,
  and basin-wide Böttcher left-inverse input) from current Bottcher/dynamical facts.
  One side-condition was reduced further: basin-wide Böttcher left-inverse now
  follows from `HasLeftInverseOn (quadratic_map c) ...` via
  `bottcher_left_inverse_on_basin_of_quadratic_left_inverse`.
  The older global-`sqrt` variant is now formally ruled out and should be treated
  as closed/dead.
- [ ] Step 3: Replace the direct axiom call in `Mlc/MainConjecture.lean`
  with the derived extension-bridge route (`..._of_extension_iter` / `..._of_extension_hyp`).
  The direct call is no longer embedded in the main proof body, but the wrapper
  theorem still instantiates via `Quadratic.quadratic_map_iter_eq_imp_eq`; this
  needs to be replaced by a constructed route from Step 1/2 data.
- [ ] Step 4: Re-run `make check` and `scripts/verify_output.sh` and confirm
  `MLC.Quadratic.quadratic_map_iter_eq_imp_eq` disappears from the output list.
- [ ] Step 5 (optional strengthening): complete the stronger global properness/degree-one route
  to injectivity on full basin with fully canonical hypotheses.

## Validation checklist for completion
- [ ] `rg -n "Quadratic\\.quadratic_map_iter_eq_imp_eq\\b" Mlc` returns no production use-site
  in the main MLC theorem path.
- [ ] `make check` output omits `MLC.Quadratic.quadratic_map_iter_eq_imp_eq`.
- [ ] README axiom block matches the new `make check` output.
  with fully canonical hypotheses.
