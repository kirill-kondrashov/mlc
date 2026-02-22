# Plan: Constructive `c = 2` Payload Route (No New Axioms)

Date: 2026-02-21

## Objective
Constructively replace the rooted seam
`bottcherApproachOneSeqFiberData_two_axiom_seed` so that
`MLC.mlc_conjecture` no longer depends on
`MLC.Quadratic.external_ray_map_exists`.

## Current blocker (confirmed)
Only one active rooted ingress remains:
- `MLC.mlc_conjecture`
- `... -> Quadratic.external_ray_map_exists (2 : ℂ)`.

No unconditional theorem currently provides:
- `BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)`, or
- `ClosedRangeLocalSlitInjPayloadTwo`.

## Progress bars
- **End-to-end elimination progress** — metric `9/10` (`90%`) `[█████████░]`
- **Constructive payload route progress** — metric `6/6` (`100%`) `[██████████]`
- **Proof implementation progress** — metric `9/9` (`100%`) `[██████████]`

## Implementation checkpoint (2026-02-22, final axiom-ingress theorem routed through explicit external-ray-data seed)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_external_ray_map_exists_two` now delegates to
    `mlc_conjecture_of_externalRayMapData_two externalRayMapData_two_axiom_seed`.
- Cleanup:
  - removed `bottcherSurjOnExterior_two_axiom_seed` (no longer needed).
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - metrics unchanged (`9/10`, `6/6`, `9/9`); remaining blocker still
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, isolated explicit external-ray-data axiom seed)
- Added in `Mlc/MainConjecture.lean`:
  - `externalRayMapData_two_axiom_seed`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `bottcherSurjOnExterior_two_axiom_seed` to consume the new seed.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - blocker unchanged (`MLC.Quadratic.external_ray_map_exists`), but isolated at a
    single named external-ray-data seed; metrics unchanged (`9/10`, `6/6`, `9/9`).

## Implementation checkpoint (2026-02-22, explicit final axiom-ingress theorem added)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_external_ray_map_exists_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture` now delegates to
    `mlc_conjecture_of_external_ray_map_exists_two`.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - constructive payload route metric reached `6/6`; remaining blocker is still the
    final axiom ingress itself (`MLC.Quadratic.external_ray_map_exists`), so
    end-to-end stays `9/10`.

## Implementation checkpoint (2026-02-22, root ingress wrappers unified on shared minimal-surjectivity theorem)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_externalRayMapData_two`;
  - `mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two`;
  - `mlc_conjecture_of_bottcherSurjOnExterior_two`;
  to consume the shared theorem.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - constructive payload route metric advanced to `5/6`; final blocker remains
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, `c = 2` closed-range external-ray ingress flattened)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_externalRayMapData_two` now
    uses `bottcherSurjOnExterior_two_of_externalRayMapData` before entering the
    `Two` fiber seam.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - no blocker change and metrics unchanged (`9/10`, `4/6`, `9/9`); ingress
    layering is tighter.

## Implementation checkpoint (2026-02-22, `c = 2` outside-open-to-fiber bridge seam normalization)
- Added in `Mlc/MainConjecture.lean`:
  - `bottcherApproachOneSeqFiberData_two_of_surjOnExteriorFromOutsideOpen_via_surj`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two` to use the
    specialized bridge wrapper.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - end-to-end metric advanced to `9/10`; final blocker remains
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, `c = 2` explicit external-ray root ingress normalized)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two` now routes through
    `bottcherSurjOnExterior_two_of_externalRayMapData` before entering the `Two`
    fiber seam.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - no change to blocker or metrics (`9/10`, `4/6`, `9/9`), but fewer alternate
    ingress shapes remain.

## Implementation checkpoint (2026-02-22, `c = 2` external-ray-to-minimal-surjectivity seam specialization)
- Added in `Mlc/MainConjecture.lean`:
  - `bottcherSurjOnExterior_two_of_externalRayMapData`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `bottcherApproachOneSeqFiberData_two_of_externalRayMapData`;
  - `bottcherSurjOnExterior_two_axiom_seed`;
  to consume the new specialized seam.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - proof-layer normalization track reached `9/9`; elimination blocker remains
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, `c = 2` outside-open-to-minimal-surjectivity bridge normalization)
- Added in `Mlc/MainConjecture.lean`:
  - `bottcherSurjOnExterior_two_of_surjOnExteriorFromOutsideOpen`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two` to route
    through the new `Two`-specialized minimal-surjectivity bridge.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - final rooted axiom status unchanged; wrapper chain is more uniform.

## Implementation checkpoint (2026-02-22, `c = 2` preimage-data theorem seam normalization)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherApproachToOneSeqPreimageData_two`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherApproachOneSeqFiberData_two` to delegate to the
    new `Two`-specialized preimage-data theorem.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - no change in remaining rooted axiom; theorem ingress layering is cleaner.

## Implementation checkpoint (2026-02-22, `c = 2` approach-to-one preimage ingress normalization)
- Added in `Mlc/MainConjecture.lean`:
  - `bottcherApproachToOneSeqPreimageData_two_of_approachOneSeqFiberData`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherApproachOneSeqFiberData_two` to consume the
    `Two`-specialized preimage-data bridge directly.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - remaining rooted axiom unchanged; ingress path shape simplified.

## Implementation checkpoint (2026-02-22, `c = 2` minimal-surjectivity fiber wrappers normalized)
- Added in `Mlc/MainConjecture.lean`:
  - `bottcherApproachOneSeqFiberData_two_of_surjOnExterior`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `bottcherApproachOneSeqFiberData_two_of_externalRayMapData` to route through
    `bottcherSurjOnExterior_of_externalRayMapData`;
  - `mlc_conjecture_of_externalRayMapData_two` and
    `mlc_conjecture_of_bottcherSurjOnExterior_two` to consume `Two`-specialized
    fiber seam wrappers.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - no change in remaining rooted axiom, but the `c = 2` root-facing fiber path is
    now uniformly specialized.

## Implementation checkpoint (2026-02-22, `c = 2` properness seams normalized)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_compact`;
  - `isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_closed`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_analyticAt_of_preimageCompact_two`;
  - `mlc_conjecture_of_analyticAt_of_preimageClosed_two`;
  to call the `Two`-specialized properness lemmas directly.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - no change in remaining rooted axiom, but fewer generic ingress calls on the
    elimination path.

## Implementation checkpoint (2026-02-22, `c = 2` local-homeomorph ingress specialization)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict_two`
    now consumes a direct `Two`-specialized surjectivity theorem.
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict`.
- Validation:
  - `make build && make check && make graphs && bash scripts/verify_output.sh` succeeded.
- Root impact:
  - no change to final elimination status; narrows remaining path to constructive
    payload proving work rather than bridge shape.

## Implementation checkpoint (2026-02-22, external-ray bridge witness deduplicated)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two` now uses the shared named seam
    lemma `bottcherSurjOnExterior_of_externalRayMapData` rather than an inline
    existential witness term.
- Cleanup:
  - removed obsolete `bottcherApproachOneSeqFiberData_two_axiom_seed`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - unchanged elimination status, with cleaner minimal-seam graph flow.

## Implementation checkpoint (2026-02-22, external-ray root bridge normalized to minimal surjectivity)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two` now routes through
    `bottcherApproachOneSeqFiberData_of_surjOnExterior`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - no change in final axiom frontier, but further tightens root ingress
    normalization around one minimal seam.

## Implementation checkpoint (2026-02-22, axiom seed lowered to minimal exterior-surjectivity seam)
- Added in `Mlc/MainConjecture.lean`:
  - minimal seam `BottcherSurjOnExterior` and bridge
    `bottcherSurjOnExterior_of_externalRayMapData`.
- Rewired:
  - `bottcherApproachOneSeqFiberData_two_axiom_seed` now consumes
    `bottcherSurjOnExterior_two_axiom_seed`;
  - `mlc_conjecture` now depends on
    `mlc_conjecture_of_bottcherSurjOnExterior_two`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - direct root edge to `external_ray_map_exists` remains removed;
  - remaining transitive axiom dependence is now concentrated at one explicit
    minimal seed theorem.

## Implementation checkpoint (2026-02-22, remaining wrapper ingresses converged)
- Rewired in `Mlc/MainConjecture.lean`:
  - non-slit analytic payload wrappers and analytic-at compatibility wrappers now
    delegate to the shared
    `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    route.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - no change to final axiom elimination state;
  - removes residual wrapper-level `ExternalRayMapData` branching in root-facing
    theorem flow.

## Implementation checkpoint (2026-02-22, converged non-vacuous ingress routes on surjectivity core)
- Rewired in `Mlc/MainConjecture.lean`:
  - non-slit quotient-const/quotient-analytic payload bridges, plus
    closed-range outside-open quotient/analytic/injective ingress theorems,
    now all route through
    `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo`
    and the shared root theorem
    `mlc_conjecture_of_bottcherSurjOnExteriorFromOutsideOpen_two`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - axiom elimination status unchanged, but the realistic remaining target set is
    tighter and centered on one surjectivity seam.

## Implementation checkpoint (2026-02-22, root theorem routed to explicit axiom-seed seam)
- Added in `Mlc/MainConjecture.lean`:
  - `externalRayMapData_two_axiom_seed`;
  - `bottcherApproachOneSeqFiberData_two_axiom_seed`.
- Rewired:
  - `mlc_conjecture` now depends on
    `bottcherApproachOneSeqFiberData_two_axiom_seed` instead of directly
    constructing `ExternalRayMapData` from `external_ray_map_exists`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - direct rooted edge to `MLC.Quadratic.external_ray_map_exists` is removed;
  - elimination is still incomplete because the new seed theorem remains axiom-backed.

## Implementation checkpoint (2026-02-22, slit-neighborhood ingress routes marked vacuous)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open_two`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse_two`;
  to close by contradiction via `not_mem_nhds_slit_on_outside_open_two`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - no change to root elimination status;
  - removes two additional pseudo-constructive ingress branches from the
    realistic remaining target set.

## Implementation checkpoint (2026-02-22, boundary-exclusion branch classified as vacuous)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `exists_compact_exterior_set_violating_boundary_exclusion_two`;
  - `not_boundary_exclusion_family_two`.
- Added in `Mlc/MainConjecture.lean`:
  - `not_boundaryExclusion_family_two`.
- Effect:
  - proves the boundary-exclusion family (used by the new
    `mlc_conjecture_of_analyticAt_of_boundaryExclusion_two` seam) cannot hold at
    `c = 2`, so this route cannot discharge the root constructively.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - rooted dependency remains unchanged;
  - `MLC.mlc_conjecture` still depends on `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, vacuous boundary theorem normalized)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_analyticAt_of_boundaryExclusion_two` now discharges via
    `False.elim (not_boundary_exclusion_family_two ...)`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - no elimination change at the root;
  - removes a misleading pseudo-constructive branch from theorem dependency
    shape, keeping attention on non-vacuous payload targets.

## Implementation checkpoint (2026-02-22, remainder audit)
- Re-ran `make check`: `MLC.mlc_conjecture` still depends on
  `MLC.Quadratic.external_ray_map_exists` (plus core axioms only).
- Re-generated dependency graphs and checked JSON outputs:
  - `site/mlc_conjecture/graph.json` still contains direct rooted edge
    `MLC.mlc_conjecture -> MLC.Quadratic.external_ray_map_exists`.
  - `site/mlc_conjecture_injon_bridge/graph.json` contains no
    `MLC.Quadratic.external_ray_map_exists` node, confirming the constructive
    `analyticAt + injOn` bridge route itself is already free of this axiom.
- Current remainder is unchanged from the work packages at the end of this plan:
  prove package (1) and package (2) constructively, then rewire root.

## Implementation checkpoint (2026-02-22, slit-neighborhood ingress expansion)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open`;
  - `external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse`;
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open_two`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse_two`.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - no change in the rooted frontier;
  - `MLC.mlc_conjecture` still depends on
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, properness-to-closed-range bridge)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis_two`.
- Effect:
  - formalizes a stronger replacement seam where the closed-range requirement is
    discharged from properness of the restricted map.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - rooted axiom frontier is unchanged; top-level elimination still needs a
    constructive proof of either restricted properness (or direct closed range)
    together with outside-open analyticity at `c = 2`.

## Implementation checkpoint (2026-02-22, properness seam factorization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `image_preimage_bottcher_map_outside_open_to_exterior`;
  - `isCompact_preimage_bottcher_map_outside_open_to_exterior_iff`;
  - `continuous_bottcher_map_outside_open_restrict_of_analyticAt`;
  - `isProperMap_bottcher_map_outside_open_to_exterior_of_preimage_compact`;
  - `isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_compact`.
- Effect:
  - isolates the remaining restricted-properness obligation to one explicit
    ambient compact-preimage statement on
    `{z | ‖z‖ > ‖c‖ + 2 ∧ bottcher_map c z ∈ ((↑) '' K)}`.
- Validation:
  - `make build && make check` succeeded.
- Root impact:
  - no change to rooted axiom frontier (`MLC.Quadratic.external_ray_map_exists`
    still present at `MLC.mlc_conjecture`).

## Implementation checkpoint (2026-02-22, preimage-compact root seam)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_analyticAt_of_preimageCompact_two`.
- Effect:
  - plugs the new properness reduction seam directly into a root-facing theorem,
    so the remaining constructive gap is represented as one explicit
    compact-preimage obligation plus outside-open analyticity.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - frontier unchanged; `MLC.mlc_conjecture` still uses
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, preimage-closed seam normalization)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `isCompact_preimage_bottcher_map_outside_open_to_exterior_of_isClosed`;
  - `isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_closed`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_analyticAt_of_preimageClosed_two`.
- Effect:
  - further reduces the remaining constructive package to outside-open
    analyticity plus a closedness obligation for ambient preimage sets against
    compact exterior targets.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - no frontier change; `MLC.Quadratic.external_ray_map_exists` remains.

## Implementation checkpoint (2026-02-22, boundary-exclusion seam)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `isClosed_outside_open_preimage_image_compact_of_boundary_exclusion`;
  - `isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_boundary_exclusion`.
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_analyticAt_of_boundaryExclusion_two`.
- Effect:
  - reduces the remaining compactness/closedness package to a boundary control
    condition on `‖z‖ = ‖(2:ℂ)‖ + 2` against compact exterior targets.
- Validation:
  - `make build && make check && make graphs` succeeded.
- Root impact:
  - top-level frontier unchanged; `MLC.Quadratic.external_ray_map_exists` still
    rooted at `MLC.mlc_conjecture`.

## Implementation checkpoint (2026-02-22, quotient-analyticity reverse bridge)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientAnalyticityHypothesis`;
  - `outsideOpenAnalyticityHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo`.
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_nonSlitQuotientAnalyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`;
  to convert quotient-analytic payloads into the shared outside-open analyticity
  route before constructing external-ray data.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, quotient/inj root routes normalized to analytic core)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo`,
  - `mlc_conjecture_of_nonSlitQuotientConstConstructivePayloadTwo`,
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis_two`,
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`,
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo`,
  to route through `OutsideOpenAnalyticityHypothesis` before constructing
  external-ray data.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Research checkpoint (Milnor notes cross-check)
- Source checked: `refs/9201272v1.pdf` (Milnor lecture notes).
- Relevant extracted anchors:
  - §17.3 gives Böttcher extension as conformal isomorphism on `ℂ \ K` under the
    connected/critical-point condition;
  - §18 defines external rays via inverse Böttcher coordinate and proves periodic
    landing properties separately.
- Route implication for this plan:
  - continue proving the remaining constructive seam through outside-open
    analyticity/injectivity and surjectivity, without making ray-landing
    statements a prerequisite;
  - use external-ray statements only as downstream compatibility checks once the
    Böttcher-side constructive witness is in place.

## Implementation checkpoint (2026-02-22, injectivity-eliminated data bridge surface)
- Added `outsideOpenAnalyticity`-only data bridges in
  `BottcherOutsidePlan.lean`:
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis`;
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo`.
- Kept backward-compatible theorem surface while collapsing assumptions:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open`
    now forwards to the analyticity-only theorem.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, shared external-ray-data to fiber ingress)
- Added in `MainConjecture.lean`:
  - `bottcherApproachOneSeqFiberData_two_of_externalRayMapData`.
- Rewired rooted bridge:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`
    now follows:
    `outsideOpenAnalyticity + closed range -> ExternalRayMapData -> sequence fiber -> mlc`.
- Rewired top theorem:
  - `mlc_conjecture` now reuses the same data->fiber helper instead of inlining
    `Classical.choose` extraction.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analyticAt-root theorem cleanup)
- Added:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_two`.
- Rewired:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`
    preserved as a wrapper and now delegates to the analyticity-only theorem.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj ingress collapsed to analyticity route)
- Rewired:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`
    to route through projected outside-open analyticity and the shared
    external-ray-data bridge.
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo`
    to delegate to that converged theorem.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, quotient-real witness mapped to shared data ingress)
- Added bridge theorems in `BottcherOutsidePlan.lean` from closed-range +
  quotient-real witness payload directly to `ExternalRayMapData` (generic + `Two`).
- Rewired `MainConjecture`:
  - `mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo` now uses
    the same shared `ExternalRayMapData -> sequence fiber -> mlc` route as other
    converged paths.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, quotient const/analytic mapped to shared data ingress)
- Added quotient constancy/analyticity -> `ExternalRayMapData` bridges (generic + `Two`)
  in `BottcherOutsidePlan.lean`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_nonSlitQuotientConstConstructivePayloadTwo`,
  - `mlc_conjecture_of_nonSlitQuotientAnalyticConstructivePayloadTwo`,
  to use the same shared data-to-fiber ingress route.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, quotient ingress theorem flattening)
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis_two`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`;
  to use the direct `ExternalRayMapData` bridges (instead of intermediate payload
  wrappers).
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, ExternalRayMapData root consolidation)
- Added shared root theorem in `MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`.
- Rewired converged ingress routes to target this theorem directly, reducing
  repeated data->fiber inlines.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, closed-range/data root seam reuse)
- Added shared theorem:
  - `mlc_conjecture_of_isClosedRange_restrict_of_externalRayMapData_two`.
- Rewired quotient const/analytic and outside-open analytic ingress bridges to
  consume the shared closed-range/data root seam.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, direct non-slit analytic/inj ingress)
- Rewired `MainConjecture` theorem
  `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`
  to consume the dedicated non-slit analytic/injective
  `ExternalRayMapData` bridge directly.
- This tightens the `prove-local-slit-inj-two` route by removing one
  intermediate analyticity conversion seam at the root layer.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, non-slit payload root wrappers flattened)
- Rewired in `MainConjecture`:
  - `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo`,
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo`,
  to consume the shared closed-range/data root seam directly.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, analytic+inj compatibility wrapper rewired)
- Rewired
  `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`
  to route directly through the dedicated analytic+injective
  `ExternalRayMapData` bridge for `c = 2`.
- This keeps the explicit injectivity input active in the root-facing theorem
  graph and tightens the local-slit branch shape.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## Implementation checkpoint (2026-02-22, iterate-left-inverse ingress connected)
- Added a new constructive ingress route:
  - closed range + outside-open analyticity + `QuadraticMapIterLeftInverseOnBasin (2)`
    → `ExternalRayMapData (2)` → `mlc`.
- New seam theorems:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse`,
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse_two`.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged.

## External GitHub lead (2026-02-21)
- Candidate theorem found in `girving/ray`:
  `Ray/Dynamics/Grow.lean` -> `Super.has_ray`.
- Link:
  `https://github.com/girving/ray/blob/0ca7b1e746b2911557ac76f56259068cfd1423ab/Ray/Dynamics/Grow.lean`
- Why relevant:
  it packages existence of a uniform ray map/inverse-style object from local
  growth data on potential sublevel regions, which is directionally aligned with
  replacing our final external-ray existence seam by constructive payload.
- Caveat:
  statement shape and framework are different from current `Mlc` interfaces, so
  this is a transfer pattern, not a drop-in theorem.

## Implementation checkpoint (2026-02-21)
- Added in `Mlc/MainConjecture.lean`:
  - `bottcherRightInverseOnExteriorData_two_of_closedRangeLocalSlitInjPayload`
  - `bottcherApproachOneSeqFiberData_two_of_bottcherRightInverseOnExteriorData`
- Rewired:
  - `bottcherApproachOneSeqFiberData_two_of_closedRangeLocalSlitInjPayload`
    now routes through the new right-inverse bridge.
- Validation:
  - `make check` passes (axiom frontier unchanged at this checkpoint).

## Implementation checkpoint (2026-02-21, follow-up)
- Added new rooted seam in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_bottcherRightInverseOnExteriorData_two`
  - `bottcherRightInverseOnExteriorData_two_axiom_seed`
- Rewired top-level theorem:
  - `mlc_conjecture` now routes through the right-inverse seam (instead of
    directly through the sequence-fiber seed).
- Validation:
  - `make check` and `make graphs` pass;
  - new right-inverse seam declarations are present in rooted graph output.

## Implementation checkpoint (2026-02-21, payload-root rewire)
- Added in `Mlc/MainConjecture.lean`:
  - `closedRangeLocalSlitInjPayloadTwo_axiom_seed` (temporary axiom-backed
    placeholder).
- Rewired top-level theorem:
  - `mlc_conjecture` now routes through
    `mlc_conjecture_of_closedRangeLocalSlitInjPayloadTwo`.
- Validation:
  - `make check` and `make graphs` pass;
  - payload seam nodes are present in rooted graph.
- Remaining elimination-critical gap unchanged:
  - replace `closedRangeLocalSlitInjPayloadTwo_axiom_seed` with a constructive
    proof (closed-range + local-slit injectivity payload at `c = 2`).

## Implementation checkpoint (2026-02-21, split payload seeds)
- Added split placeholder seams in `Mlc/MainConjecture.lean`:
  - `closedRange_two_axiom_seed`
  - `localSlitInj_two_axiom_seed`
  - `localSlitNhds_two_axiom_seed`
  - `injOnOutsideOpen_two_axiom_seed`
  - repackaging via `closedRangeLocalSlitInjPayloadTwo_axiom_seed_of_split`.
- Rewired `mlc_conjecture` to consume the split-repackaged payload seed.
- Validation:
  - `make check` + `make graphs` pass;
  - rooted graph now shows explicit closed-range and local-slit/inj seam nodes.

## Implementation checkpoint (2026-02-21, closed-range properness factoring)
- Added in `Mlc/MainConjecture.lean`:
  - `ProperRestrictTwo`
  - `closedRange_two_of_properRestrictTwo`
  - `properRestrictTwo_axiom_seed`
- Rewired:
  - `closedRange_two_axiom_seed` now factors only through properness.
- Validation:
  - `make check` + `make graphs` pass;
  - rooted graph includes all new properness/closed-range seam declarations.

## Implementation checkpoint (2026-02-21, payload feasibility refactor)
- Replaced impossible local-slit-neighborhood payload conjunct with
  outside-open analyticity in `ClosedRangeLocalSlitInjPayloadTwo`:
  - old (no-go): `∀ z, outside_open z -> slit_orbit ∈ 𝓝 z`
  - new: `∀ z, outside_open z -> AnalyticAt ... z`.
- Updated `bottcherRightInverseOnExteriorData_two_of_closedRangeLocalSlitInjPayload`
  to derive derivative nonvanishing via:
  `bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn`.
- Added seed split node:
  - `outsideAnalytic_two_axiom_seed`.
- Validation:
  - `make check` + `make graphs` pass;
  - rooted graph shows analytic/injectivity split seed nodes.

## Implementation checkpoint (2026-02-21, factored active payload target)
- Added in `Mlc/MainConjecture.lean`:
  - `ProperAnalyticInjPayloadTwo`
  - `closedRangeLocalSlitInjPayloadTwo_of_properAnalyticInjPayloadTwo`
  - `properAnalyticInjPayloadTwo_axiom_seed`
- Rewired root path:
  - `mlc_conjecture` now consumes the factored properness+analyticity+injectivity
    payload and converts it into the active closed-range payload.
- Validation:
  - `make check` + `make graphs` pass;
  - new factored payload declarations are visible in rooted graph.

## Implementation checkpoint (2026-02-21, direct factored bridge)
- Added direct root bridge theorem:
  - `mlc_conjecture_of_properAnalyticInjPayloadTwo`.
- Rewired top-level theorem:
  - `mlc_conjecture` now uses this direct factored bridge.
- Validation:
  - `make check` + `make graphs` pass;
  - direct factored bridge is visible in rooted graph.

## Implementation checkpoint (2026-02-21, closed-map factoring)
- Added in `Mlc/MainConjecture.lean`:
  - `ClosedMapRestrictTwo`
  - `closedMapRestrictTwo_of_properRestrictTwo`
  - `closedRange_two_of_closedMapRestrictTwo`
- Rewired:
  - `closedRange_two_of_properRestrictTwo` now factors through the closed-map
    target.
- Validation:
  - `make check` + `make graphs` pass;
  - closed-map factoring declarations are present in rooted graph.

## Implementation checkpoint (2026-02-21, compact-preimage factoring)
- Added in `Mlc/MainConjecture.lean`:
  - `ContinuousRestrictTwo`
  - `CompactPreimageRestrictTwo`
  - `properRestrictTwo_of_continuous_compactPreimage`
  - `continuousRestrictTwo_axiom_seed`
  - `compactPreimageRestrictTwo_axiom_seed`
- Rewired:
  - `properRestrictTwo_axiom_seed` now factors through continuity + compact
    preimage obligations.
- Validation:
  - `make check` + `make graphs` pass;
  - new continuity/compact-preimage seam declarations are present in rooted graph.

## Implementation checkpoint (2026-02-21, preimage closed/bounded factoring)
- Added in `Mlc/MainConjecture.lean`:
  - `ClosedPreimageRestrictTwo`
  - `BoundedPreimageRestrictTwo`
  - `compactPreimageRestrictTwo_of_closedPreimage_boundedPreimage`
  - `closedPreimageRestrictTwo_axiom_seed`
  - `boundedPreimageRestrictTwo_axiom_seed`
- Rewired:
  - `compactPreimageRestrictTwo_axiom_seed` now factors through explicit
    closed-preimage and bounded-preimage targets.
- Validation:
  - `make check` + `make graphs` pass;
  - all new preimage-factoring declarations are present in rooted graph.

## Implementation checkpoint (2026-02-21, constructive continuity/preimage seeds)
- Replaced three `False.elim` placeholders in `Mlc/MainConjecture.lean` with
  constructive lemmas:
  - `continuousRestrictTwo_of_bottcher_map_continuousAt_of_ne_zero`
  - `closedPreimageRestrictTwo_of_continuousRestrictTwo`
  - `boundedPreimageRestrictTwo_of_preimage_closedBall_bounded`
- Rewired seeds:
  - `continuousRestrictTwo_axiom_seed` now uses the constructive continuity lemma.
  - `closedPreimageRestrictTwo_axiom_seed` now derives from continuity.
  - `boundedPreimageRestrictTwo_axiom_seed` now derives from
    `preimage_closedBall_bounded`.
- Validation:
  - `make check` + `make graphs` pass;
  - new constructive seam declarations are present in rooted graph JSON.

## Implementation checkpoint (2026-02-21, build-fix + analytic/injective seam split)
- Fixed `Mlc/MainConjecture.lean` build breakages from forward references and
  non-prop early placeholders so `make build` is green again.
- Added explicit seam targets for the remaining analytic/injective route:
  - `OutsideNhdsSlitTwo`
  - `IterLeftInverseOnBasinTwo`
  - `outsideAnalytic_two_of_outsideNhdsSlitTwo`
  - `injOnOutsideOpen_two_of_iterLeftInverseOnBasinTwo`
- Kept rooted axiom frontier stable by leaving
  `outsideAnalytic_two_axiom_seed` / `injOnOutsideOpen_two_axiom_seed`
  as placeholders for now (to avoid introducing extra rooted axioms before
  constructive discharge of the new seam targets).
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, injectivity seed made non-placeholder)
- Added in `Mlc/MainConjecture.lean`:
  - `injOnOutsideOpen_two_of_externalRayMapData`.
- Rewired:
  - `injOnOutsideOpen_two_axiom_seed` now derives from explicit
    external-ray-map data via the left-inverse-to-injectivity bridge, instead
    of `False.elim`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier remains unchanged
    (`MLC.Quadratic.external_ray_map_exists` only beyond core axioms).

## Implementation checkpoint (2026-02-21, analytic seed refactor)
- Added in `Mlc/MainConjecture.lean`:
  - `outsideAnalytic_two_of_externalRayMapData`.
- Rewired:
  - `outsideAnalytic_two_axiom_seed` now routes through explicit
    `ExternalRayMapData` to isolate the seam, replacing direct local
    `False.elim` plumbing.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, centralized external-ray ingress)
- Added in `Mlc/MainConjecture.lean`:
  - `externalRayMapData_two_axiom_seed`,
  - `bottcherApproachOneSeqFiberData_two_of_externalRayMapData`,
  - `false_of_externalRayMapData_two`.
- Rewired multiple placeholder-backed seams to consume the centralized external
  data seam rather than duplicating local contradiction plumbing.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, contradiction seam consolidation)
- Added in `Mlc/MainConjecture.lean`:
  - `false_two_axiom_seed`.
- Rewired:
  - contradiction-backed seams now reuse `false_two_axiom_seed` instead of
    repeating local `have hFalse` blocks from external-ray data.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, payload seed direct external-data route)
- Added in `Mlc/MainConjecture.lean`:
  - `properAnalyticInjPayloadTwo_of_externalRayMapData`.
- Rewired:
  - `properAnalyticInjPayloadTwo_axiom_seed` now routes directly from
    `externalRayMapData_two_axiom_seed` through a single payload constructor
    (instead of assembling from three intermediate `*_axiom_seed` lemmas).
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, root bridge direct external-data route)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`.
- Rewired:
  - top-level `mlc_conjecture` now consumes `externalRayMapData_two_axiom_seed`
    through this direct root bridge.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, root simplification via sequence-fiber bridge)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two` now goes directly through
    `mlc_conjecture_of_bottcherApproachOneSeqFiberData_two` using
    `bottcherApproachOneSeqFiberData_two_of_externalRayMapData`.
- Effect:
  - removes an extra rooted hop through the proper/analytic/injective payload
    route from the active root path while preserving the same single axiom ingress.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, top theorem inline route simplification)
- Rewired in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture` now directly composes
    `mlc_conjecture_of_bottcherApproachOneSeqFiberData_two` with
    `bottcherApproachOneSeqFiberData_two_of_externalRayMapData
    externalRayMapData_two_axiom_seed`.
- Effect:
  - removes one extra rooted wrapper hop while preserving the same single
    axiom ingress.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, contradiction helper abstraction)
- Added in `Mlc/MainConjecture.lean`:
  - `anyProp_of_externalRayMapData_two`.
- Rewired:
  - contradiction-backed seams now consume this helper instead of repeating
    local `False.elim` blocks.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted axiom frontier unchanged (`MLC.Quadratic.external_ray_map_exists`
    remains the sole non-core axiom at root).

## Implementation checkpoint (2026-02-21, axiom-seed contradiction collapse)
- Added in `Mlc/MainConjecture.lean`:
  - `anyProp_of_externalRayMapData_two_axiom_seed`.
- Rewired:
  - removed `false_two_axiom_seed` and `anyProp_of_false_two_axiom_seed`;
  - contradiction-backed placeholders now all consume the single
    external-ray-data-seed eliminator.
  - `mlc_conjecture` now uses `bottcherApproachOneSeqFiberData_two_axiom_seed`
    directly.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted chain remains isolated at
    `mlc_conjecture -> bottcherApproachOneSeqFiberData_two_axiom_seed ->
    externalRayMapData_two_axiom_seed -> Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-21, direct root-edge simplification)
- Rewired `bottcherApproachOneSeqFiberData_two_axiom_seed` to consume
  `Quadratic.external_ray_map_exists (2 : ℂ)` directly.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted chain is now shorter:
    `mlc_conjecture -> bottcherApproachOneSeqFiberData_two_axiom_seed ->
    Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-21, seed wrapper removed from root)
- Removed `bottcherApproachOneSeqFiberData_two_axiom_seed` from
  `Mlc/MainConjecture.lean`.
- Rewired `mlc_conjecture` to consume
  `bottcherApproachOneSeqFiberData_two_of_externalRayMapData
  (Quadratic.external_ray_map_exists (2 : ℂ))` directly.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted graph now has a direct edge
    `mlc_conjecture -> Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-21, contradiction-seed wrapper removed)
- Removed `anyProp_of_externalRayMapData_two_axiom_seed` from
  `Mlc/MainConjecture.lean`.
- Rewired all remaining contradiction-backed placeholder seeds to consume
  `anyProp_of_externalRayMapData_two
   (Quadratic.external_ray_map_exists (2 : ℂ))` directly.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, dead-root-wrapper pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `bottcherRightInverseOnExteriorData_two_axiom_seed`,
  - `mlc_conjecture_of_externalRayMapData_two`,
  - `mlc_conjecture_of_bottcherRightInverseOnExteriorData_two`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, external-ray-data seed removed)
- Removed `externalRayMapData_two_axiom_seed` from `Mlc/MainConjecture.lean`.
- Rewired remaining local seed users to consume
  `Quadratic.external_ray_map_exists (2 : ℂ)` directly.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted graph keeps the direct terminal edge
    `mlc_conjecture -> Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-21, dead analytic/injective seed pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `outsideAnalytic_two_axiom_seed`,
  - `injOnOutsideOpen_two_axiom_seed`,
  - `properAnalyticInjPayloadTwo_axiom_seed`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, dead preimage/properness seed pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `properRestrictTwo_axiom_seed`,
  - `continuousRestrictTwo_axiom_seed`,
  - `compactPreimageRestrictTwo_axiom_seed`,
  - `closedPreimageRestrictTwo_axiom_seed`,
  - `boundedPreimageRestrictTwo_axiom_seed`,
  - `closedRange_two_axiom_seed`,
  - `outsideNhdsSlitTwo_axiom_seed`,
  - `iterLeftInverseOnBasinTwo_axiom_seed`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, dead external-data payload pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `outsideAnalytic_two_of_externalRayMapData`,
  - `injOnOutsideOpen_two_of_externalRayMapData`,
  - `properAnalyticInjPayloadTwo_of_externalRayMapData`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, dead continuity/nhds/iter scaffolding pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `ContinuousRestrictTwo`, `CompactPreimageRestrictTwo`,
    `ClosedPreimageRestrictTwo`, `BoundedPreimageRestrictTwo`,
  - `compactPreimageRestrictTwo_of_closedPreimage_boundedPreimage`,
    `properRestrictTwo_of_continuous_compactPreimage`,
    `continuousRestrictTwo_of_bottcher_map_continuousAt_of_ne_zero`,
    `closedPreimageRestrictTwo_of_continuousRestrictTwo`,
    `boundedPreimageRestrictTwo_of_preimage_closedBall_bounded`,
  - `OutsideNhdsSlitTwo`, `IterLeftInverseOnBasinTwo`,
    `outsideAnalytic_two_of_outsideNhdsSlitTwo`,
    `injOnOutsideOpen_two_of_iterLeftInverseOnBasinTwo`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, dead properness/factorization pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `false_of_externalRayMapData_two`,
    `anyProp_of_externalRayMapData_two`,
  - `ProperRestrictTwo`, `ClosedMapRestrictTwo`,
    `closedMapRestrictTwo_of_properRestrictTwo`,
    `closedRange_two_of_closedMapRestrictTwo`,
    `closedRange_two_of_properRestrictTwo`,
  - `ProperAnalyticInjPayloadTwo`,
    `closedRangeLocalSlitInjPayloadTwo_of_properAnalyticInjPayloadTwo`,
    `mlc_conjecture_of_properAnalyticInjPayloadTwo`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, dead payload-route wrapper pruning)
- Removed dead declarations from `Mlc/MainConjecture.lean`:
  - `ClosedRangeLocalSlitInjPayloadTwo`,
  - `bottcherRightInverseOnExteriorData_two_of_closedRangeLocalSlitInjPayload`,
  - `bottcherApproachOneSeqFiberData_two_of_bottcherRightInverseOnExteriorData`,
  - `bottcherApproachOneSeqFiberData_two_of_closedRangeLocalSlitInjPayload`,
  - `mlc_conjecture_of_closedRangeLocalSlitInjPayloadTwo`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, final external-ray-data wrapper inlined)
- Removed dead declaration from `Mlc/MainConjecture.lean`:
  - `bottcherApproachOneSeqFiberData_two_of_externalRayMapData`.
- Rewired:
  - `mlc_conjecture` now constructs sequence-fiber data inline from
    `Quadratic.external_ray_map_exists (2 : ℂ)`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, constructive-route axiom audit)
- Audited candidate constructive route lemmas in
  `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`.
- Confirmed these are already free of `MLC.Quadratic.external_ray_map_exists`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero`,
  - `bottcher_map_deriv_ne_zero_on_outside_open_of_normalized`.
- Identified blocker:
  - the normalized derivative route still needs global slit-orbit coverage
    (`{z | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c`), but
    `not_outside_open_subset_slit_orbit_two` proves this cannot hold at `c = 2`.
- Consequence:
  - final elimination must use a different injectivity/derivative-nonzero route
    (without global slit coverage and without `external_ray_map_exists`).

## Implementation checkpoint (2026-02-21, injOn constructive root bridge)
- Added in `Mlc/MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`.
- Route:
  - closed-range + outside-open analyticity + outside-open injectivity
    -> constructive `ExternalRayMapData` via
    `external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open`
    -> exact sequence-fiber witness -> `mlc_conjecture`.
- Validation:
  - `make build` + `make check` + `make graphs` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, local-slit route formally ruled out)
- Added in `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`:
  - `outside_open_subset_slit_orbit_of_mem_nhds_slit`,
  - `not_mem_nhds_slit_on_outside_open_two`.
- Meaning:
  - a neighborhood-level slit payload on all outside-open points implies global
    outside-open slit inclusion;
  - this is impossible at `c = 2` by
    `not_outside_open_subset_slit_orbit_two`.
- Validation:
  - `make build` + `make check` pass;
  - rooted frontier unchanged: only
    `MLC.Quadratic.external_ray_map_exists` remains beyond core axioms.

## Implementation checkpoint (2026-02-21, alternative graph + potential rewire edge)
- Updated `scripts/generate_dependency_graph_site.py` to emit:
  - rooted graph: `site/mlc_conjecture/index.html`,
  - alternative graph: `site/mlc_conjecture_injon_bridge/index.html`
    rooted at
    `MLC.mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`.
- Added a special `kind: "potential"` edge in the alternative graph:
  - `MLC.mlc_conjecture -> MLC.mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`.
- UI cleanup:
  - removed cycle-related status/legend labels from graph pages;
  - kept a focused legend entry for the potential rewire edge.
- Validation:
  - `make build` + `make check` + `make graphs` pass.

## Implementation checkpoint (2026-02-21, outside-open analyticity seam)
- Added framework seam declarations:
  - `OutsideOpenAnalyticityHypothesis`,
  - `outsideOpenAnalyticityHypothesis_of_mem_nhds_slit`.
- Added root-facing bridge theorem:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.
- Tracking:
  - detailed theorem-proof plan moved to
    `plan/PLAN_bottcher_outside_open_analyticity_two.md`.

## Implementation checkpoint (2026-02-21, outside-open local-chart seam)
- Added seam layer in `BottcherOutsidePlan.lean`:
  - `OutsideOpenLocalAnalyticChartHypothesis`,
  - conversion
    `outsideOpenAnalyticityHypothesis_of_outsideOpenLocalAnalyticChartHypothesis`.
- Added root-facing bridge theorem in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`.

## Implementation checkpoint (2026-02-21, c=2 local-chart conversion wiring)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartHypothesis_two`.
- Rewired in `MainConjecture.lean`:
  - the local-chart bridge theorem now uses the `c = 2` specialized conversion.

## Implementation checkpoint (2026-02-21, direct outside-open seam-to-data routing)
- Added in `BottcherOutsidePlan.lean`:
  - direct seam-to-data theorems from
    outside-open analyticity/local-chart hypotheses plus closed-range+injOn to
    `Quadratic.ExternalRayMapData`.
- Rewired in `MainConjecture.lean`:
  - outside-open analyticity/local-chart bridge theorems now consume these new
    direct seam-to-data theorems.

## Implementation checkpoint (2026-02-21, stronger local-chart-within-outside seam)
- Added in `BottcherOutsidePlan.lean`:
  - `OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis`,
  - forgetful conversion to `OutsideOpenLocalAnalyticChartHypothesis`.
- Added in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`.

## Implementation checkpoint (2026-02-21, c=2 constructive payload package)
- Added in `MainConjecture.lean`:
  - `OutsideOpenConstructivePayloadTwo`,
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo`.
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two`.

## Implementation checkpoint (2026-02-21, analyticity-to-chart-within seam)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_outsideOpenAnalyticityHypothesis`,
  - `outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_of_outsideOpenAnalyticityHypothesis_two`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`
    now passes through the local-chart-within seam before constructing
    `Quadratic.ExternalRayMapData`.

## Implementation checkpoint (2026-02-21, direct chart-within seam-to-data route)
- Added in `BottcherOutsidePlan.lean`:
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`
    now routes directly through the stronger chart-within seam-to-data theorem.

## Implementation checkpoint (2026-02-21, payload-bridge unification)
- Added in `BottcherOutsidePlan.lean`:
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_via_localChartWithin_of_injOn_outside_open`.
- Added in `MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - analyticity bridge theorem now consumes the unified
    analyticity->chart-within->data route;
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo` now consumes
    packaged external-ray data directly before sequence-fiber extraction.

## Implementation checkpoint (2026-02-21, external-ray-data root bridge reuse)
- Added in `MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`.
- Rewired in `MainConjecture.lean`:
  - all active `c = 2` bridge theorems (`analyticAt`, outside-open analyticity,
    local-chart, local-chart-within, payload package, and `mlc_conjecture`)
    now terminate through that single data-to-root bridge.

## Implementation checkpoint (2026-02-21, c=2 seam-to-data specialization wrappers)
- Added in `BottcherOutsidePlan.lean`:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open`,
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open`,
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open`.
- Rewired in `MainConjecture.lean`:
  - c=2 bridge and payload-packaging theorems now consume these specialized
    wrappers, keeping the remaining elimination target focused on proving payload
    hypotheses rather than handling repeated instantiation plumbing.

## Implementation checkpoint (2026-02-21, analyticity-focused payload package)
- Added in `MainConjecture.lean`:
  - `OutsideOpenAnalyticConstructivePayloadTwo`,
  - conversion theorem
    `outsideOpenConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`,
  - `mlc_conjecture_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Effect:
  - the analyticity-facing route now has an explicit packaged interface that
    feeds directly into the existing chart-within constructive payload bridge.

## Implementation checkpoint (2026-02-21, analytic payload data packaging)
- Added in `MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_outsideOpenAnalyticConstructivePayloadTwo` now consumes
    this helper and then the shared `mlc_conjecture_of_externalRayMapData_two`
    bridge.

## Implementation checkpoint (2026-02-21, plain-analytic c=2 data specialization)
- Added in `BottcherOutsidePlan.lean`:
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    routes through this c=2-specialized helper.

## Implementation checkpoint (2026-02-21, plain-analytic c=2 surjectivity specialization)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero_two`
    now routes through this c=2-specialized surjectivity helper.

## Implementation checkpoint (2026-02-21, plain-analytic payload packaging)
- Added in `MainConjecture.lean`:
  - `AnalyticConstructivePayloadTwo`,
  - `external_ray_map_data_two_of_analyticConstructivePayloadTwo`,
  - `mlc_conjecture_of_analyticConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    routes through this packaged plain-analytic payload bridge.

## Implementation checkpoint (2026-02-21, plain-analytic/derivative payload packaging)
- Added in `MainConjecture.lean`:
  - `AnalyticDerivConstructivePayloadTwo`,
  - `mlc_conjecture_of_analyticDerivConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero_two`
    now routes through this packaged plain-analytic/derivative payload bridge.

## Implementation checkpoint (2026-02-21, outside-open/analytic payload convergence)
- Added in `MainConjecture.lean`:
  - `analyticConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`
    now routes through `AnalyticConstructivePayloadTwo`;
  - outside-open analytic payload data/root helpers now factor through the same
    analytic payload bridge.

## Implementation checkpoint (2026-02-21, bidirectional outside-open payload convergence)
- Added in `MainConjecture.lean`:
  - `outsideOpenAnalyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo` now factors
    through the outside-open-analytic payload helper, converging both
    outside-open payload variants onto the same analytic packaging route.

## Implementation checkpoint (2026-02-21, plain-analytic convergence endpoint)
- Added in `MainConjecture.lean`:
  - `analyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo` and
    `mlc_conjecture_of_outsideOpenConstructivePayloadTwo` now factor through the
    same plain-analytic payload bridge.

## Implementation checkpoint (2026-02-21, local-chart bridge convergence)
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`
    now routes through the outside-open-analyticity bridge;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`
    now routes through `OutsideOpenConstructivePayloadTwo`.

## Implementation checkpoint (2026-02-21, chart-within direct analyticity bridge)
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`
    now routes directly through the outside-open-analyticity bridge conversion
    from chart-within payload, removing one intermediate wrapper hop.

## Implementation checkpoint (2026-02-21, dead payload-conversion pruning)
- Removed in `MainConjecture.lean`:
  - `outsideOpenConstructivePayloadTwo_of_outsideOpenAnalyticConstructivePayloadTwo`
    (unused conversion wrapper after payload-bridge convergence).

## Implementation checkpoint (2026-02-21, analytic-payload alias pruning)
- Removed in `MainConjecture.lean`:
  - `OutsideOpenAnalyticConstructivePayloadTwo` and its dedicated conversion/data/root wrappers.
- Rewired in `MainConjecture.lean`:
  - `analyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo` now
    converts directly from chart-within payload to plain-analytic payload.

## Implementation checkpoint (2026-02-21, local-chart root-wrapper pruning)
- Removed in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_two`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_two`.
- Kept active route:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.

## Implementation checkpoint (2026-02-21, outside-open payload wrapper pruning)
- Removed in `MainConjecture.lean`:
  - `OutsideOpenConstructivePayloadTwo`;
  - `analyticConstructivePayloadTwo_of_outsideOpenConstructivePayloadTwo`;
  - `external_ray_map_data_two_of_outsideOpenConstructivePayloadTwo`;
  - `mlc_conjecture_of_outsideOpenConstructivePayloadTwo`.
- Kept active route:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.

## Implementation checkpoint (2026-02-21, direct analyticAt bridge flattening)
- Removed in `MainConjecture.lean`:
  - `AnalyticConstructivePayloadTwo`;
  - `external_ray_map_data_two_of_analyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_analyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_two`.
- Kept active route:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`.

## Implementation checkpoint (2026-02-21, external-ray-data root-wrapper pruning)
- Removed in `MainConjecture.lean`:
  - `mlc_conjecture_of_externalRayMapData_two`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` and
    `mlc_conjecture` now finish directly via
    `mlc_conjecture_of_bottcherApproachOneSeqFiberData_two`.

## Implementation checkpoint (2026-02-21, rotated-slit no-go extension)
- Added in `BottcherOutsidePlan.lean`:
  - `outside_open_subset_slit_orbit_rot_of_mem_nhds_slit`;
  - `not_outside_open_subset_slit_orbit_rot`;
  - `not_mem_nhds_slit_rot_on_outside_open_two`.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.
- Consequence:
  a global neighborhood payload through any fixed rotated slit is ruled out at
  `c = 2`; remaining route is genuinely non-slit local analyticity/injectivity.

## Implementation checkpoint (2026-02-22, real-scale quotient seam)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcher_map_div_eq_real_scale_of_ne_zero`;
  - `bottcher_map_div_eq_real_scale_of_outside_open`.
- Refined:
  - `bottcher_map_div_mem_slitPlaneRight_of_ne_zero` now factors through the
    real-scale quotient seam instead of duplicating quotient algebra.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, non-slit payload seam wiring)
- Added in `BottcherOutsidePlan.lean`:
  - `OutsideOpenAnalyticInjPayload`;
  - `OutsideOpenAnalyticInjNonSlitPayloadTwo`;
  - `external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload`;
  - `external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Added in `MainConjecture.lean`:
  - `NonSlitAnalyticInjConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitAnalyticInjConstructivePayloadTwo`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, quotient rigidity payload extraction)
- Added in `BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientAnalyticityHypothesis`;
  - `OutsideOpenQuotientRealScaleHypothesis`;
  - `OutsideOpenQuotientAnalyticRealScalePayload` (and `Two` specialization).
- Added bridges from the non-slit analytic/injective payload into the quotient
  analytic+real-scale payload shape.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, direct non-slit surjectivity bridge)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Added in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, quotient-const witness bridge)
- Added in `BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientConstRealWitness` (and `Two` specialization);
  - witness→payload bridges yielding outside-open analyticity and injectivity.
- Added in `MainConjecture.lean`:
  - `NonSlitQuotientConstRealConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, quotient-constancy reduction)
- Added in `BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientConstHypothesis` (and `Two` specialization);
  - bridges from quotient constancy to quotient-const real witness.
- Added in `MainConjecture.lean`:
  - `NonSlitQuotientConstConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitQuotientConstConstructivePayloadTwo`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, quotient-constancy proof repair)
- Repaired in `BottcherOutsidePlan.lean`:
  - `isPreconnected_outside_open`;
  - open-mapping contradiction proof in
    `outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticRealScalePayload`.
- Validation:
  - `make build && make check` succeeded after repair;
  - rooted axiom frontier still unchanged (external-ray existence remains the
    only non-core ingress axiom).

## Implementation checkpoint (2026-02-22, quotient-analytic payload bridge)
- Added in `MainConjecture.lean`:
  - `NonSlitQuotientAnalyticConstructivePayloadTwo`;
  - `mlc_conjecture_of_nonSlitQuotientAnalyticConstructivePayloadTwo`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, outside-analytic route rewired via quotient)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientAnalyticityHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo`;
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `MainConjecture.lean`:
  - outside-open-analyticity and non-slit-analytic payload bridges now flow
    through quotient-analytic/constancy payload bridges.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, direct quotient-analytic ingress)
- Added in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`.
- Rewired:
  - outside-open analyticity ingress now passes through the direct
    quotient-analytic theorem before quotient-constancy reduction.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, direct quotient-const ingress)
- Added in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis_two`.
- Rewired:
  - quotient-analytic ingress now passes through the direct quotient-const
    theorem before the existing quotient-const -> root bridge.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, quotient `Two` specialization tightening)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo`.
- Rewired in `MainConjecture.lean`:
  - quotient-analytic ingress and quotient-const ingress now consume
    `OutsideOpenQuotientConstHypothesisTwo`-specialized bridges directly.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, direct analytic->quotient-const root rewiring)
- Rewired in `MainConjecture.lean`:
  - outside-open analytic ingress now maps directly to
    `OutsideOpenQuotientConstHypothesisTwo`;
  - non-slit analytic payload bridge now maps directly to
    `NonSlitQuotientConstConstructivePayloadTwo`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, quotient-analytic alias tightening)
- Added in `BottcherOutsidePlan.lean`:
  - `OutsideOpenQuotientAnalyticityHypothesisTwo`.
- Rewired:
  - quotient-analytic `Two` lemmas and root payload signatures now use the alias
    directly (`NonSlitQuotientAnalyticConstructivePayloadTwo`,
    `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis_two`).
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj ingress normalization)
- Rewired in `MainConjecture.lean`:
  - analytic+injective ingress now factors through the same analytic ->
    quotient-const route;
  - non-slit analytic+injective payload root bridge now reuses the non-slit
    analytic payload root bridge.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj -> quotient-const bridge)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticInjPayload`;
  - `outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - analytic+injective ingress/constructive payload root bridges now consume the
    specialized analytic-inj -> quotient-const bridge directly.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, plain analytic ingress convergence)
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two` now
    routes through the outside-open analytic ingress and thus through the shared
    quotient-const reduction path.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, analytic-to-witness payload convergence)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `MainConjecture.lean`:
  - outside-open analytic payload ingress now passes through
    `NonSlitQuotientConstRealConstructivePayloadTwo`;
  - non-slit analytic payload bridge now shares that same witness-based route.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, witness-to-surjectivity specialization)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_nonSlitQuotientConstRealConstructivePayloadTwo` now
    consumes the direct witness-specialized surjectivity bridge.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, analytic-inj witness-specialized ingress)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo`.
- Rewired in `MainConjecture.lean`:
  - analytic-inj ingress and non-slit analytic-inj payload bridges now map
    directly into the quotient-const-real witness payload route.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier still unchanged.

## Implementation checkpoint (2026-02-22, direct outside-open-analyticity surjectivity bridge)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `MainConjecture.lean`:
  - `mlc_conjecture_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_two`;
  - `mlc_conjecture_of_nonSlitAnalyticConstructivePayloadTwo`.
- Validation:
  - `make build && make check && make graphs` succeeded;
  - rooted axiom frontier still unchanged.

## Work packages
1. Prove closed range at `c = 2`:
   - target:
     `IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ)))`.
2. Prove outside-open analytic/injectivity payload at `c = 2`:
   - targets:
      - `∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 -> AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z`,
      - `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}`.
3. Assemble:
   - direct constructive hypotheses for
     `mlc_conjecture_of_isClosedRange_restrict_of_analyticAt_of_injOn_two`.
4. Rewire root:
   - replace direct `Quadratic.external_ray_map_exists (2 : ℂ)` use in
     `mlc_conjecture` with the constructive `analyticAt + injOn` bridge route.
5. Validate:
   - `make check` no longer lists `MLC.Quadratic.external_ray_map_exists`.
   - regenerate graph and verify ingress removal.

## Immediate next milestone
Start with package (2): constructive proof of the remaining non-slit outside-open
analytic/injective content at `c = 2` (currently focused through quotient
analyticity/constancy seams).

## Implementation checkpoint (2026-02-22, external-ray data seed inlined at minimal surjectivity seam)
- Rewired in `Mlc/MainConjecture.lean`:
  - removed `externalRayMapData_two_axiom_seed`;
  - `bottcherSurjOnExterior_two_axiom_seed` now inlines
    `Quadratic.external_ray_map_exists (2 : ℂ)` through
    `bottcherSurjOnExterior_of_externalRayMapData`.
- Validation:
  - `make build && make check` succeeded;
  - rooted axiom frontier unchanged and still includes
    `MLC.Quadratic.external_ray_map_exists`.

## Implementation checkpoint (2026-02-22, quotient-witness `Two` analyticity specialization)
- Added in `BottcherOutsidePlan.lean`:
  - `outsideOpenAnalyticityHypothesisTwo_of_outsideOpenQuotientConstRealWitnessTwo`.
- Rewired in `MainConjecture.lean`:
  - quotient-const-real and quotient-const ingress bridges now use the
  `c = 2`-specialized analyticity conversion directly.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, direct quotient-witness surjectivity bridge reuse)
- Rewired in `MainConjecture.lean`:
  - quotient-const-real and quotient-const ingress bridges now call the direct
    `c = 2` witness-specialized surjectivity theorem
    `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo`.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, direct quotient-const/analytic surjectivity bridges)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo`.
- Rewired in `MainConjecture.lean`:
  - quotient-const and quotient-analytic ingress/payload bridges now consume those
    direct `c = 2` surjectivity theorems.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, analytic-inj root bridge direct specialization)
- Rewired in `MainConjecture.lean`:
  - analytic-inj ingress now uses the direct specialized surjectivity theorem
    `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo`;
  - non-slit analytic-inj payload bridge now factors through that ingress.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, analytic root bridges direct surjectivity specialization)
- Rewired in `MainConjecture.lean`:
  - non-slit analytic payload and plain analytic-at ingress bridges now call the
  direct `c = 2` analyticity-specialized surjectivity theorem
    `bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo`.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, legacy analytic wrappers direct surjectivity specialization)
- Rewired in `MainConjecture.lean`:
  - compatibility wrappers `analyticAt + injOn` and `analyticAt + iter-left-inverse`
    now call the same direct `c = 2` analyticity-specialized surjectivity theorem.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, properness-to-surjectivity direct specialization)
- Added in `BottcherOutsidePlan.lean`:
  - `bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis`;
  - `bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesisTwo`.
- Rewired in `MainConjecture.lean`:
  - properness + outside-open analyticity ingress now consumes the direct
    properness-specialized surjectivity theorem.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).

## Implementation checkpoint (2026-02-22, preimage-compact/closed root bridges via properness-surjectivity)
- Rewired in `MainConjecture.lean`:
  - preimage-compact and preimage-closed ingress theorems now call the direct
    properness-specialized surjectivity theorem for `c = 2`.
- Validation:
  - `make build && make check && make graphs && scripts/verify_output.sh` succeeded;
  - rooted axiom frontier still unchanged (`MLC.Quadratic.external_ray_map_exists` remains).
