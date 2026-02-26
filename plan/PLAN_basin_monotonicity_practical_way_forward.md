# Plan: Basin Monotonicity Practical Way Forward

## Goal
- [ ] Remove dependence on `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`
  by replacing Euclidean-ray monotonicity requirements with a true Böttcher-ray
  monotonicity/inversion path.

## Locked Model Constraints
- [x] Outside-open analyticity route is blocked
  (`not_outsideOpenAnalyticityHypothesisTwo`).
- [x] Degree-one strict-mono-free ingress route is blocked
  (`not_greenFunctionDegreeOneIngressTwo`).
- [x] Known injectivity-source strict-mono-free route is blocked
  (`not_knownInjOnOutsideOpenSourceCandidateTwo`).
- [x] This plan now treats those routes as closed and focuses on direct
  monotonicity/uniqueness proofs only.

## Parallel Placement
- [x] Assigned to **Track A (Strict-Mono Elimination)** in
  `PLAN_axiom_elimination_status.md`.
- [x] Works in parallel with:
  `PLAN_prove_green_function_radial_monotonicity.md` and
  `PLAN_eliminate_green_function_strictMono_along_ray_basin_seam.md`.

## Progress Implemented
- [x] Added a seam-free conditional Green-inversion route in
  `GreenFunctionRayInversion`:
  `external_ray_map_exists_two_via_green_function_of_injOn_outside_open`.
- [x] Added a MainConjecture wrapper:
  `external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open`.
- [x] Re-routed
  `external_ray_map_exists_two_constructive_of_green_function_of_iter_left_inverse`
  through outside-open injectivity (instead of the strict-mono uniqueness seam).
- [x] Added a seam-minimal Green inversion constructor that consumes anchored
  uniqueness directly:
  `external_ray_map_exists_two_via_green_function_of_uniquePreimageSeam`,
  and rewired
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`
  through it (removing an intermediate injectivity detour on that path).
- [x] Routed strict-mono-seeded root injectivity witness through the same
  uniqueness-seam bridge:
  `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded`.
- [x] Repointed downstream strict-mono-seeded wrapper callsites to the
  centralized green-function-seeded uniqueness alias
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_greenFunctionStrictMonoAlongRayBasinTwo_seed`.
- [x] Re-routed `injOn_outside_open_two_of_greenRayLogGtAnchorTwoSeam` to use
  the centralized green-function-seeded uniqueness alias directly (instead of
  the older injectivity-seeded compatibility alias).
- [x] Repointed the remaining compatibility uniqueness alias
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_injOn_outside_open`
  to the centralized green-function-seeded uniqueness witness.
- [x] Reduced strict-mono-seeded root payload alias depth by routing
  `rootSeedPayloadTwo_strictMono_seeded` through
  `rootSafeOutsideOpenInjWitnessTwo_strictMono_seeded` directly.
- [x] Reduced strict-mono-seeded root bundle alias depth:
  `rootSeedPairTwo_strictMono_seeded` now consumes
  `rootSeedPayloadTwo_strictMono_seeded` directly and `rootSeedPairTwo_seed`
  aliases `rootSeedPairTwo_strictMono_seeded`.
- [x] Reduced strict-mono-seeded root selector and root theorem alias depth:
  `externalRayMapData_two_root_seed_strictMono_seeded`,
  `mlc_conjecture_of_externalRayMapData_two_root_seed_strictMono_seeded`, and
  `mlc_conjecture` now consume `rootSeedPayloadTwo_strictMono_seeded`
  directly.
- [x] Removed obsolete strict-mono-seeded alias shims now made redundant by
  the centralized seed path:
  `rootSafeOutsideOpenInjWitnessTwo_seed`,
  `greenRayUniquePreimageTwoAnchorSeam_strictMono_seeded_of_rootSafeOutsideOpenInjWitnessTwo`,
  `rootSeedPayloadTwo_seed`,
  `rootSeedPairTwo_seed`.
- [ ] Root theorem `external_ray_map_exists_two_constructive` still uses the
  legacy strict-mono path and is the remaining call site to replace.

## A. Replace Theorem Target
- [ ] Introduce a new seam/target statement for strict monotonicity along
  Böttcher rays (not Euclidean rays `ρ • u`).
- [ ] Mark/deprecate the Euclidean-ray seam usage points in
  `GreenFunctionRayInversion` and downstream call sites.

### Exact Replacement (Current Draft)
- [x] Introduced seam-free conditional replacement already implemented:
  `external_ray_map_exists_two_via_green_function_of_injOn_outside_open`
  with signature:
  `theorem ... (hlog_gt_anchor : GreenRayLogGtAnchorTwoSeam)
               (h_inj_outside : InjOn bottcher_map outside_open) :
               ExternalRayMapData (2 : ℂ)`.
- [ ] Final target still to implement:
  replace Euclidean-ray strict-mono uniqueness with a Böttcher-ray uniqueness
  theorem, then make `external_ray_map_exists_two_via_green_function` itself
  seam-free (no injectivity assumption needed).

### Call-Site Patch Status
- [x] Added MainConjecture wrapper:
  `external_ray_map_exists_two_constructive_of_green_function_of_injOn_outside_open`.
- [x] Patched
  `external_ray_map_exists_two_constructive_of_green_function_of_iter_left_inverse`
  to route through the wrapper above.
- [x] Added rooted conditional wrappers:
  `mlc_conjecture_of_green_function_of_injOn_outside_open_two` and
  `mlc_conjecture_of_green_function_of_iter_left_inverse_two`.
- [x] Added CP5/direct-witness Green-route wrappers:
  `external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo`,
  `external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo_unconditional`,
  `external_ray_map_exists_two_constructive_of_green_function_of_directProperLocalWitnessTwo`,
  plus rooted `mlc_conjecture_*` counterparts.
- [x] Refactored direct-witness Green wrapper to bypass CP5/landing detour:
  `external_ray_map_exists_two_constructive_of_green_function_of_directProperLocalWitnessTwo`
  now uses direct outside-open injectivity from
  `injOn_outside_open_two_of_directProperLocalWitnessTwo_constructive`,
  removing unnecessary dependency on `extended_ray_map_continuous` from that branch.
- [x] Added explicit no-landing variants:
  `external_ray_map_exists_two_constructive_of_green_function_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen`
  and `mlc_conjecture_of_green_function_of_cp5ResidualTwo_of_not_externalRayLandsOutsideOpen`,
  so `extended_ray_map_continuous` is only pulled by the unconditional alias.
- [x] Added a new frontier-safe degree-one bridge target in `MainConjecture`:
  `ProperLocalDegreeOneFiberWitnessTwo` and wrappers
  `injOn_outside_open_two_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness`,
  `external_ray_map_exists_two_constructive_of_green_function_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness`,
  `mlc_conjecture_of_green_function_of_isProperMap_isLocalHomeomorph_of_degreeOneFiberWitness`.
  This isolates the remaining constructive gap to proving a singleton-fiber
  witness without relying on `external_ray_map_exists`.
- [x] Added packaged ingress:
  `GreenFunctionDegreeOneIngressTwo` and root wrapper
  `mlc_conjecture_of_green_function_degreeOneIngressTwo`.
  Axiom scan shows this route uses only
  `Quot.sound`, `propext`, `Classical.choice`, and
  `greenRayLogGtAnchorTwo_axiom_seed` (no `external_ray_map_exists`,
  no `green_function_strictMono_along_ray_basin_seam`).
- [x] Investigated restricted-map degree-one witness route (`DirectProperLocalWitnessTwo`
  + singleton fiber on `bottcher_map_outside_open_to_exterior`): reverted prototype.
  Current blocker is theorem shape: the available
  `injective_of_isProperMap_isLocalHomeomorph_of_exists_natCard_fiber_eq_one`
  is specialized to `ℂ → ℂ`, so it cannot be applied directly to subtype maps.
- [x] Added restricted singleton-fiber witness constructor from outside-open
  injectivity:
  `restrictProperLocalDegreeOneFiberWitnessTwo_of_injOn_outside_open`.
  Axiom scan: only `Quot.sound`, `propext`, `Classical.choice`.
  This keeps the restricted degree-one route prepared while the subtype
  injectivity theorem-shape gap is addressed.
- [x] Added global singleton-fiber bridge from properness + outside-open
  injectivity:
  `properLocalDegreeOneFiberWitnessTwo_of_isProperMap_of_injOn_outside_open`,
  plus external-ray-data wrapper
  `external_ray_map_exists_two_constructive_of_green_function_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open`,
  plus rooted wrapper
  `mlc_conjecture_of_green_function_of_isProperMap_isLocalHomeomorph_of_injOn_outside_open_two`.
  This removes the need to pass an explicit `hdeg1` witness when `hproper`
  and outside-open injectivity are already available.
- [ ] Remaining root call site:
  `external_ray_map_exists_two_constructive` (still calls the legacy theorem
  requiring Euclidean-ray strict monotonicity).
- [x] Verified that routing root through
  `injOn_outside_open_two_axiom_seed` is frontier-unsafe:
  it reintroduces `MLC.Quadratic.external_ray_map_exists`, so this route is
  explicitly disallowed and was reverted.

## B. Build Böttcher-Ray Infrastructure
- [ ] Define a Böttcher-ray parameterization on basin points:
  `R_{c,θ}(t) := φ_c^{-1}(exp(t + iθ))` (or an equivalent existing encoding).
- [ ] Add/locate lemmas that `R_{c,θ}(t)` is in basin and is well-defined on the
  intended domain.
- [ ] Prove/route the identity `green_function c (R_{c,θ}(t)) = t`.

## C. Monotonicity + Uniqueness via Böttcher Coordinate
- [ ] Prove strict monotonicity along Böttcher rays from `G(R_{c,θ}(t)) = t`.
- [ ] Refactor uniqueness lemmas to use Böttcher-ray parameter `t` instead of
  Euclidean radial parameter `ρ`.
- [ ] Replace `exists_unique_ray_preimage_*` proofs that currently rely on
  `green_function_strictMono_along_ray_basin_seam`.

## D. Patch Constructive External-Ray Path
- [x] Update `external_ray_map_exists_two_via_green_function` (and variants) to
  use the new uniqueness route.
  Status: added
  `external_ray_map_exists_two_via_green_function_of_uniquePreimageSeam` in
  `GreenFunctionRayInversion.lean`; routed
  `external_ray_map_exists_two_constructive_of_greenRayLogGtAnchorTwoSeam_of_uniquePreimageSeam`
  and
  `external_ray_map_exists_two_constructive_of_greenFunctionStrictMonoAlongRayBasinTwoSeam`
  through uniqueness-seam constructors in `MainConjecture.lean`.
- [ ] Remove obsolete dependencies on Euclidean-ray monotonicity assumptions.

## E. Frontier Cleanup
- [ ] Remove `green_function_strictMono_along_ray_basin_seam` from
  `Mlc/Quadratic/Complex/Axioms.lean` once unused.
- [ ] Re-run `make build` and `make check`.
- [ ] Confirm `check_axioms.lean` no longer reports
  `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`.

## Notes / Risks
- [ ] Verify each current "ray" usage means Euclidean ray vs Böttcher ray;
  convert only the arguments that need strict monotonicity/uniqueness.
- [ ] Keep `MLC.Quadratic.external_ray_map_exists` out of this proof path.
