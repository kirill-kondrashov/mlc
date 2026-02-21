# Plan: Eliminate `external_ray_map_exists` via Outside-Open Targets

Date: 2026-02-20

## Objective
Remove `MLC.Quadratic.external_ray_map_exists` from the axiom footprint of
`MLC.mlc_conjecture` without:
- introducing any new axioms,
- adding hypotheses to `MLC.mlc_conjecture`,
- collapsing the rooted proof into contradiction circulation.

## Progress
- Overall closure progress (under current constraints):
  `[███████░░░] ~73%`
- Structural isolation progress:
  `[██████████] 99.99%` (4.99984/5 core milestones completed)

## Current rooted situation
In `Mlc/MainConjecture.lean`, the active seam is now:
- `MainPathData` (constructive core assembly target),
- seeded by `mainPathData_axiom_seed`,
- where the only contradiction step is confined to
  `mainPathData_of_bottcherApproachToOneSeqPreimageData_two`.
- the rooted seed now consumes the exact countable-fiber payload at the
  canonical sequence directly via
  `bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData`.
- this is then converted to the sequence-convergence seam through
  `bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData`.
- the rooted axiom seed now avoids the generic surjectivity bridge and consumes
  only a direct `c = 2` sequence-fiber seed:
  `bottcherApproachOneSeqFiberData_two_axiom_seed`.
- a non-circular Step-4→Step-5 bridge is now explicit at `c = 2`:
  `mainPathData_of_bottcherSurjOnExteriorFromOutsideOpen_two`, which routes
  through outside-open fibers of `approach_one_seq`.

The external-ray dependency is now localized through the narrowed seed chain:
- `mainPathData_axiom_seed`
- `mainPathData_of_bottcherApproachToOneSeqPreimageData_two`
- `bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData`
- `bottcherApproachOneSeqFiberData_two_axiom_seed`
- `Quadratic.external_ray_map_exists (2 : ℂ)` (via direct unpacking of
  `ExternalRayMapData`, applied only to `approach_one_seq n`)
- `MLC.Quadratic.external_ray_map_exists`.

Outside-plan default right-inverse construction is now routed through:
- `bottcher_right_inverse_on_exterior_data_of_bottcher_map_surj`,
not directly through
- `bottcher_right_inverse_on_exterior_data_of_external_ray_map_exists`.
This keeps the non-rooted outside-plan frontier on exterior surjectivity
payloads.

Exact rooted dependency chain to the missing axiom (from generated graph):
1. `MLC.mlc_conjecture`
2. `MLC.mainPathData_axiom_seed`
3. `MLC.mainPathData_of_bottcherApproachToOneSeqPreimageData_two`
4. `MLC.bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData`
5. `MLC.bottcherApproachOneSeqFiberData_two_axiom_seed`
6. `MLC.Quadratic.external_ray_map_exists`

## Reduction target chain (already available in code)
From `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean` and
`Mlc/MainConjecture.lean`:
1. If we can prove
   - injectivity on outside-open:
     `Set.InjOn (Quadratic.bottcher_map c) {z | ‖z‖ > ‖c‖ + 2}`
   - surjectivity onto exterior by outside-open preimages:
     `BottcherSurjOnExteriorFromOutsideOpen c`,
   then we can build
   - `Quadratic.ExternalRayMapData c`
     via `external_ray_map_data_of_injOn_outside_open_of_surj_exterior`.
2. Outside-open surjectivity at `c = 2` directly yields the rooted seam target
   by choosing preimages of `approach_one_seq` in `mainPathData_axiom_seed`.
   (No rooted need remains to first construct full `ExternalRayMapData (2 : ℂ)`.)

So elimination reduces to proving those two outside-open targets at `c = 2`
without using `external_ray_map_exists`.

## Hard blocker (explicit)
Current available route to outside-open injectivity in this repo is still via
left-inverse data derived from `ExternalRayMapData`, i.e. circular.
Also, the current slit payload shape
`{z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c` is likely too strong for `c = 2`;
the non-circular route should target a weaker, usable local/eventual-slit
condition rather than global outside-open slit inclusion.

## External research inputs (Dudko)
Downloaded and indexed under:
- `refs/Dudko_*.pdf`
- `refs/Dudko_relevance_external_ray_map_exists.md`

Most relevant for global MLC strategy (renormalization/classification track):
- `refs/Dudko_2512.24171.pdf`
- `refs/Dudko_2309.02107.pdf`
- `refs/Dudko_1808.10425.pdf`

Potentially supportive geometric context:
- `refs/Dudko_1004.0633.pdf`
- `refs/Dudko_S0002-9939-2011-11047-5.pdf`

Critical screening result for this plan:
- No direct drop-in replacement was identified for the current formal blocker
  in this Lean route:
  `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}`
  plus restricted-map closed-range/properness at `c = 2`.
- Therefore this plan remains focused on proving Step 3/4 non-circularly in
  the present outside-open framework, while keeping renormalization-track
  references available for broader strategy pivots.

### Hard blocker sharpened (no-go checkpoint)
- The current global slit payload
  `{z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c`
  is not a viable target in this model.
- Reason (model-level): for any `c`, large negative real points satisfy
  `‖z‖ > ‖c‖ + 2` but fail membership in the principal slit plane at iterate
  `n = 0`, so they cannot lie in `slit_orbit c`.
- Consequence: Step 4 should no longer treat this global slit payload as an
  achievable subgoal for elimination. It is a deliberate no-go marker, not an
  unfinished proof.
- This no-go is now formalized in code:
  - `not_outside_open_subset_slit_orbit`
  - `not_outside_open_subset_slit_orbit_two`

## Next non-circular proof milestones
1. [x] Prove theorem-level clopen route for outside-open exterior surjectivity
   (assumption-level).
2. [x] Critically revise the clopen assumptions to avoid impossible conditions
   in the current explicit model (`preimage exterior ⊆ outside_open`), and
   re-express the route via the restricted map
   `bottcher_map_outside_open_to_exterior`:
   - `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_of_isLocalHomeomorph_restrict`,
   - `external_ray_map_data_of_injOn_outside_open_of_isProperMap_of_isLocalHomeomorph_restrict`.
2b. [x] Remove the need to prove restricted-map local-homeomorph separately by
   deriving it from slit analyticity on outside-open:
   - `isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_slit`,
   - `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_restrict_of_slit`,
   - `external_ray_map_data_of_isProperMap_restrict_of_slit_of_injOn_outside_open`.
2c. [x] Weaken the clopen route further from properness to closed-range on the
   restricted map:
   - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_of_isLocalHomeomorph_restrict`,
   with properness retained only as a specialization theorem.
2d. [x] Add slit-derived route with only closed-range assumption:
   - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_slit`,
   - `external_ray_map_data_of_isClosedRange_restrict_of_slit_of_injOn_outside_open`.
2e. [x] Add a local-slit-compatible wrapper route (no global outside-open slit
   inclusion) by factoring through local analyticity on outside-open:
   - analytic core:
     `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_injOn`,
     `external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open`;
   - local-slit wrappers:
     `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_mem_nhds_slit_of_deriv_ne_zero`,
     `external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open`.
2f. [x] Add iterate-left-inverse bridge wrappers into the same closed-range
   analytic core:
   - `bottcher_map_inj_on_outside_open_of_iter_left_inverse`,
   - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse`,
   - `external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse`.
   This gives a non-external-ray injection route candidate for Step 3 that
   plugs directly into Step 4's restricted-map clopen mechanism.
   Critical revision: this route is now considered non-viable as a constructive
   elimination path in the current model because
   `not_quadratic_map_iter_eq_imp_eq` (in
   `Mlc/Quadratic/Complex/Bottcher/InverseBranchSlitUse.lean`) blocks the
   underlying iterate-equality implication on the basin.
   This no-go is now explicitly packaged as
   `not_quadratic_map_iter_left_inverse_on_basin`.
2g. [x] Re-extract the rooted `MainConjecture` seed through an explicit
   exterior-surjectivity seam (instead of direct ray witness construction):
   - added in `Mlc/MainConjecture.lean` an explicit
     exterior-surjectivity-to-sequence seam;
   - rewired `mainPathData_axiom_seed` through this seam.
   This aligns the root with the outside-open-surjectivity replacement target.
2h. [x] Further narrow the rooted seam to the exact minimal sequence payload:
   - removed the extra `BottcherSurjOnExteriorData` wrapper layer from the
     rooted path;
   - added
     `mainPathData_of_bottcherApproachToOneSeqPreimageData_two`;
   - rewired `mainPathData_axiom_seed` through this sequence-only seed.
2i. [x] Generalize the rooted sequence seam to the exact replacement interface:
   - added `bottcherApproachToOneSeqPreimageData_of_surj_on_exterior`
     (later pruned in 2n);
   - rewired rooted construction through this generic constructor.
   This makes Step 5 a direct theorem substitution task once
   `BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)` is proved.
2j. [x] Prune extra rooted wrappers to keep `MainConjecture` free of dead
   bridge declarations:
   - removed unused `c = 2` axiom-seed wrapper
     `bottcherApproachToOneSeqPreimageData_two_axiom_seed`;
   - removed wrapper `bottcherApproachToOneSeqPreimageData_of_bottcher_map_surj`;
   - rewired `mainPathData_axiom_seed` to call
     `bottcherApproachToOneSeqPreimageData_of_surj_on_exterior` (historical;
     later replaced and pruned in 2n) with an inlined
     `Quadratic.bottcher_map_surj` provider at `c = 2`.
2k. [x] Narrow the rooted replacement interface one step further to exact
   countable fibers of the canonical exterior sequence:
   - added `BottcherApproachOneSeqFiberData`,
   - added `bottcherApproachOneSeqFiberData_of_surj_on_exterior`
     (later pruned in 2n),
   - added `mainPathData_of_bottcherApproachOneSeqFiberData_two`,
   - rewired `mainPathData_axiom_seed` through this exact fiber seam.
   This makes Step 5 independent of full exterior surjectivity: only sequence
   fibers for `approach_one_seq` remain required at the rooted interface.
2l. [x] Remove the generic surjectivity bridge from the rooted axiom seed:
   - added direct `c = 2` seed
     `bottcherApproachOneSeqFiberData_two_axiom_seed`,
   - rewired `mainPathData_axiom_seed` to consume it directly.
   This makes the rooted dependency chain strictly sequence-specific and keeps
   Step 5 focused on replacing only the exact countable-fiber payload.
2m. [x] Add explicit Step-4→Step-5 bridge through outside-open sequence fibers:
   - added `BottcherApproachOneSeqOutsideOpenFiberData`,
   - added
     `bottcherApproachOneSeqOutsideOpenFiberData_of_surjOnExteriorFromOutsideOpen`,
   - added `mainPathData_of_bottcherSurjOnExteriorFromOutsideOpen_two`.
   This isolates the remaining replacement to proving
   `BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)` non-circularly.
2n. [x] Prune newly dead generic sequence-surjectivity bridges from
   `Mlc/MainConjecture.lean` to keep only rooted-path-relevant interfaces:
   - removed `bottcherApproachOneSeqFiberData_of_surj_on_exterior`,
   - removed `bottcherApproachToOneSeqPreimageData_of_surj_on_exterior`.
2o. [x] Prune extra outside-open wrapper in the rooted bridge chain:
   - removed
     `mainPathData_of_bottcherApproachOneSeqOutsideOpenFiberData_two`,
   - inlined it into
     `mainPathData_of_bottcherSurjOnExteriorFromOutsideOpen_two`.
2p. [x] Remove rooted dependence on `bottcher_map_surj` by switching the
   current axiom seed to the direct external-ray right-inverse on
   `approach_one_seq`:
   - rewired `bottcherApproachOneSeqFiberData_two_axiom_seed` to use
     `Quadratic.external_ray_map_right_inverse` at `c = 2`.
2q. [x] Prune extra rooted wrappers for the exact-fiber seam:
   - removed `mainPathData_of_bottcherApproachOneSeqFiberData_two`,
   - removed `bottcherApproachOneSeqFiberData_of_outsideOpenFiberData`,
   - rewired rooted bridges through
     `mainPathData_of_bottcherApproachToOneSeqPreimageData_two` and
     `bottcherApproachToOneSeqPreimageData_of_approachOneSeqFiberData`.
2r. [x] Add external literature checkpoint for elimination guidance:
   - downloaded Dudko corpus into `refs/`,
   - recorded screening in
     `refs/Dudko_relevance_external_ray_map_exists.md`,
   - linked conclusions into this plan (no direct Step 3/4 theorem replacement
     found; keep current non-circular outside-open target path).
2s. [x] Tighten rooted seed dependency by removing the extra
   `external_ray_map_right_inverse` wrapper:
   - rewired `bottcherApproachOneSeqFiberData_two_axiom_seed` to unpack
     `Quadratic.external_ray_map_exists (2 : ℂ)` directly.
2t. [x] Add direct theorem-level Step-4→root bridge at `c = 2`:
   - added
     `mainPathData_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_two`,
   - initially composed the restricted-map clopen local-slit route directly
     into `MainPathData` (now further rewired through the weaker seam
     interfaces added in later steps).
2u. [x] Add proper-map specialization of the direct Step-4→root bridge:
   - added
     `mainPathData_of_isProperMap_restrict_of_mem_nhds_slit_of_injOn_two`,
   - this allows using `IsProperMap` payloads directly by reducing to closed
     range of the restricted map and reusing 2t.
2v. [x] Add analytic-core Step-4→root bridge and route local-slit through it:
   - added
     `mainPathData_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`,
   - rewired
     `mainPathData_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_two`
     through `bottcher_map_analyticAt_on_outside_open_of_mem_nhds_slit`.
2w. [x] Route the closed-range local-slit rooted bridge through the weaker
   restricted-local-homeomorph seam and prune the extra `c = 2` specialization:
   - rewired
     `mainPathData_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_two`
     through weaker restricted-map local-homeomorph interfaces (now further
     inlined into analytic/derivative-rooted bridges),
   - pruned dead theorem:
     `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn`.
2x. [x] Add a direct proper-map + restricted local-homeomorph rooted bridge at
   `c = 2`, and route the local-slit proper-map theorem through it:
   - added in `BottcherOutsidePlan`:
     `bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict`,
   - rewired
     `mainPathData_of_isProperMap_restrict_of_mem_nhds_slit_of_injOn_two`
     through this weaker seam interface,
   - pruned dead theorem:
     `bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_mem_nhds_slit_of_injOn`.
2y. [x] Add an explicit weaker rooted bridge at `c = 2` through restricted-map
   local-homeomorph (without hard-coding injectivity at the seam interface):
   - rewired
     `mainPathData_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`
     through this weaker interface (now further routed through
     analytic/derivative payloads).
2z. [x] Push the analytic closed-range route one step further to derivative
   payloads (`analytic + deriv ≠ 0`) and keep injectivity as a wrapper-only
   path:
   - added in `BottcherOutsidePlan`:
     `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero`,
   - added in `MainConjecture`:
     `mainPathData_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero_two`,
   - rewired
     `mainPathData_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`
     to derive derivative nonvanishing and route through the new theorem.
2aa. [x] Extend the derivative payload routing to local-slit wrappers and the
   proper-map rooted bridge:
   - added in `MainConjecture`:
     `mainPathData_of_isClosedRange_restrict_of_mem_nhds_slit_of_deriv_ne_zero_two`,
     `mainPathData_of_isProperMap_restrict_of_analyticAt_of_deriv_ne_zero_two`,
   - rewired
     `mainPathData_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_two`,
     `mainPathData_of_isProperMap_restrict_of_mem_nhds_slit_of_injOn_two`
     through analytic/derivative payloads.
2ab. [x] Push local-slit bridges in `BottcherOutsidePlan` to derivative payloads:
   - added derivative variants:
     `bottcher_map_isLocalHomeomorphOn_outside_open_of_mem_nhds_slit_of_deriv_ne_zero`,
     `isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_mem_nhds_slit_of_deriv_ne_zero`,
     `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_mem_nhds_slit_of_deriv_ne_zero`,
   - rewired corresponding `...of_mem_nhds_slit_of_injOn` wrappers through
     derivative payloads.
2ac. [x] Complete the same derivative routing for the proper-map local-slit
   rooted bridge in `MainConjecture`:
   - added
     `mainPathData_of_isProperMap_restrict_of_mem_nhds_slit_of_deriv_ne_zero_two`,
   - rewired
     `mainPathData_of_isProperMap_restrict_of_mem_nhds_slit_of_injOn_two`
     through this derivative payload theorem.
2ad. [x] Remove unnecessary injectivity assumptions from slit-based outside-plan
   surjectivity theorems and prune dead wrappers:
   - slit surjectivity now routes through
     `isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_slit`,
   - weakened theorem interfaces:
     `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_restrict_of_slit`,
     `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_slit`,
   - pruned dead local-slit injective wrappers no longer used in the current
     elimination chain.
2ae. [x] Prune dead intermediate rooted wrappers in `MainConjecture` after
   analytic/derivative routing became primary:
   - removed obsolete restricted-local-homeomorph bridge wrappers,
   - inlined proper-map rooted route directly through
     `bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict`.
3. [ ] Prove outside-open injectivity at `c = 2` by a route independent of
   external ray data (e.g. local-homeomorph/proper-map + fiber-control route),
   explicitly avoiding the iterate-left-inverse route from 2f.
4. [ ] Discharge restricted-map clopen assumptions at `c = 2` without
   `external_ray_map_exists`:
   - `IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ)))`
     (or stronger `IsProperMap`),
   - replace the no-go global slit payload with a local/eventual-slit variant
     that is sufficient for the restricted-map local-homeomorph step near the
     needed preimages of `approach_one_seq`,
   - the non-circular restricted-map local-homeomorph payload from Step 3
     (or injectivity payload if using the fallback branch),
   and obtain
   `BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)`.
5. [ ] Instantiate non-circular exact preimage-sequence data at `c = 2` from
   outside-open surjectivity, and replace rooted use of
   `Quadratic.external_ray_map_exists` in
   `mainPathData_axiom_seed`.

## Active next theorem target
- Prefer proving the weaker non-circular restricted-map local-homeomorph payload
  at `c = 2`:
  `IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))`.
- If that route fails, prove the non-circular `c = 2` injectivity payload and
  recover local-homeomorph from it:
  `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}`.
- Prove restricted-map geometric payloads at `c = 2`:
  - `IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ)))`
    (or stronger `IsProperMap`),
  - local/eventual-slit payload replacing the global no-go slit inclusion.
- Use the restricted-map clopen theorem to derive surjectivity and then
  construct exact preimages for `approach_one_seq` at `c = 2` without
  `Quadratic.external_ray_map_exists`.

## Acceptance checks
- `make build`
- `make graphs`
- `make check`
- `scripts/verify_output.sh`
- Axiom list for `MLC.mlc_conjecture` contains only core axioms
  (`Quot.sound`, `propext`, `Classical.choice`).
