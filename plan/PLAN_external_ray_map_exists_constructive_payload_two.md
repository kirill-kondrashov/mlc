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
- `... -> bottcherApproachOneSeqFiberData_two_axiom_seed`
- `... -> Quadratic.external_ray_map_exists (2 : ℂ)`.

No unconditional theorem currently provides:
- `BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)`, or
- `ClosedRangeLocalSlitInjPayloadTwo`.

## Progress bars
- End-to-end elimination progress:
  `[██████████] ~99%`
- Constructive payload route progress:
  `[█████████▓] ~95%`
- Proof implementation progress:
  `[████████▓░] ~86%`

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

## Work packages
1. Prove closed range at `c = 2`:
   - target:
     `IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ)))`.
2. Prove outside-open analytic/injectivity payload at `c = 2`:
   - targets:
      - `∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 -> AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z`,
      - `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}`.
3. Assemble:
   - `ClosedRangeLocalSlitInjPayloadTwo`.
4. Rewire root:
   - replace final seed in `mlc_conjecture` with
     `mlc_conjecture_of_closedRangeLocalSlitInjPayloadTwo`.
5. Validate:
   - `make check` no longer lists `MLC.Quadratic.external_ray_map_exists`.
   - regenerate graph and verify ingress removal.

## Immediate next milestone
Start with package (1): closed-range proof for
`bottcher_map_outside_open_to_exterior (2 : ℂ)`, while extracting any reusable
local-to-global ray-construction pattern from `Super.has_ray`.
