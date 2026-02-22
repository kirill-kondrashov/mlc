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
- End-to-end elimination progress:
  `[██████████] ~99%`
- Constructive payload route progress:
  `[██████████] ~99%`
- Proof implementation progress:
  `[██████████] ~99%`

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
Start with package (1): closed-range proof for
`bottcher_map_outside_open_to_exterior (2 : ℂ)`, while extracting any reusable
local-to-global ray-construction pattern from `Super.has_ray`.
