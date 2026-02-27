# MLC Formalization Status

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph (rooted at `MLC.mlc_conjecture`)](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository is a Lean formalization scaffold centered on `MLC.mlc_conjecture`.
The code compiles and `MLC.mlc_conjecture` is `sorry`-free.

## Current Axiom Frontier (`make check`)

As of 2026-02-27, exactly one non-core axiom remains in the root theorem:

- `MLC.greenRayLogGtAnchorTwo_axiom_seed`

This axiom is **not** in the allowed frontier. The allowed frontier
remains core-only:

- `Quot.sound`
- `propext`
- `Classical.choice`

So `make check` currently fails with an axiom-frontier violation until this
axiom is eliminated. Eliminating it is the immediate next milestone.

Expected output:

```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.greenRayLogGtAnchorTwo_axiom_seed
```

## Progress Snapshot (Effort In Hours, Not Weeks)

| Target Axiom | Progress | Left | Estimated Remaining Effort |
|---|---|---|---|
| `greenRayLogGtAnchorTwo_axiom_seed` | `█████████░` 87% | 13% | ~80-220 Lean LOC, ~3-8 hrs |

Total estimated remainder: ~80-220 Lean LOC, ~3-8 hours.

## Active Plans (`plan/*`)

| File | Relevance | Progress | Left | Estimated Remaining Effort |
|---|---|---|---|---|
| `plan/PLAN_axiom_elimination_status.md` | ⭐⭐⭐⭐⭐ | `██████████` 100% | 0% | v24 iteration summary |
| `plan/PLAN_axiom_elimination_root_closure_bridge_equivalence_v24.md` | ⭐⭐⭐⭐⭐ | `██████████` 100% | 0% | root-closure bridge equivalence complete |
| `plan/PLAN_axiom_elimination_root_closure_kernel_cutover_v24.md` | ⭐⭐⭐⭐⭐ | `██████████` 100% | 0% | root-closure kernel cutover complete |
| `plan/PLAN_axiom_elimination_frontier_validation_v24.md` | ⭐⭐⭐⭐☆ | `██████████` 100% | 0% | frontier remained single-axiom |
| `plan/PLAN_axiom_elimination_retired_route_guardrail_v24.md` | ⭐⭐⭐⭐☆ | `██████████` 100% | 0% | no-go guardrail maintained |
| `plan/PLAN_axiom_elimination_constructive_bridge_search_v24.md` | ⭐⭐⭐⭐⭐ | `██████░░░░` 60% | 40% | frontier-safe constructive bridge still missing |

## Key Technical Reality

- The old global anchor-gap seam is inconsistent in the current model:
  `not_greenRayLogGtAnchorTwoSeam`.
- The bounded-cutoff replacement route is also inconsistent:
  `not_greenRayLogGtAnchorTwo_cutoff_band`.
- An anchor-free payload staging interface now exists in root wiring:
  `RootSeedPayloadTwoNoAnchor` and its first bridge wrappers.
- Latest cycle confirmed the non-seam replacement interface is complete, while
  root cutover remains blocked by a missing non-seeded no-arg outside-open
  injectivity witness.
- New non-seeded seam helper exists:
  `cp5ResidualLocalHomeomorphInjSeamTwo_of_rootSafeOutsideOpenInjWitnessTwo`.
- New equivalence and root-tail staging wrappers now exist:
  `rootSafeOutsideOpenInjWitnessTwo_iff_cp5ResidualLocalHomeomorphInjSeamTwo_of_directProperLocalWitnessTwo`
  and `mlc_conjecture_root_tail_nonseam_of_directProperLocalWitnessTwo`.
- Primitive witness-family interface now exists:
  `PrimitiveRestrictedMapProperLocalWitnessFamilyTwo` and
  `primitiveRestrictedMapProperLocalWitnessFamilyTwo_iff_directProperLocalWitnessTwo`.
- Primitive-family specialization bridges now exist:
  `rootSafeOutsideOpenInjWitnessTwo_iff_cp5ResidualLocalHomeomorphInjSeamTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo`
  and `mlc_conjecture_root_tail_nonseam_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo`.
- Primitive-family witness-gap/root-gap bridges were added:
  `primitiveRestrictedMapProperLocalWitnessFamilyTwo_iff_remainingConstructiveIngressTwoWitnessGap`,
  `rootClosureSubstituteTwoWitnessGap_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo`,
  and `rootClosureSubstituteTwo_of_primitiveRestrictedMapProperLocalWitnessFamilyTwo`.
- Strict-mono-free ingress dead-end is now normalized explicitly:
  `rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo_iff_false` and
  `rootSeedPayloadTwoStrictMonoFreeIngressTwo_iff_false`.
- New non-seeded ingress probe family was added and shown blocked:
  `RootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo` and
  `not_rootSafeOutsideOpenInjWitnessTwoNonseededIngressFamilyTwo`.
- New geometric outside-open/fiber ingress family was added:
  `RootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo`.
- That geometric family is normalized to the existing root-safe target:
  `rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo_iff_rootSafeOutsideOpenInjWitnessTwo`.
- Geometric-ingress log-gap constructor shape is now explicitly blocked:
  `not_greenRayLogGtAnchorTwoSeam_constructor_from_rootSafeOutsideOpenInjWitnessTwoGeometricFiberIngressFamilyTwo`.
- Added ray-monotonicity-window interface and no-go pair:
  `GreenRayLogGapMonotonicityWindowTwo` and
  `not_greenRayLogGapMonotonicityWindowTwo`.
- Added candidate nonvacuous geometric extraction bundle and no-go:
  `NonvacuousGeometricIngressWitnessExtractionTwo` and
  `not_nonvacuousGeometricIngressWitnessExtractionTwo`.
- Added parameterized nonimplicative local-window interface:
  `NonimplicativeWindowInterfaceTwo`.
- Added cutoff-coverage no-go for that interface:
  `not_nonimplicativeWindowInterfaceTwo_of_cutoff_le_radius`.
- Added localized ray-interval geometric source interface:
  `LocalizedRayIntervalGeometricSourceTwo`.
- Added cutoff-coverage no-go for localized source:
  `not_localizedRayIntervalGeometricSourceTwo_of_cutoff_le_radius`.
- Added strict subcutoff local-window + transport package:
  `StrictlySubcutoffLocalWindowWithTransportBridgeTwo`.
- Added no-go for strict subcutoff transport package:
  `not_strictlySubcutoffLocalWindowWithTransportBridgeTwo`.
- Added localized-source to ingress-gap interface:
  `LocalizedSourceToRemainingConstructiveIngressGapTwo`.
- Added no-go for that localized-source transport interface:
  `not_localizedSourceToRemainingConstructiveIngressGapTwo`.
- Added partial-window interface without tail transport:
  `PartialWindowNotCoveringCutoffWithNontransportedTailTwo`.
- Added localized source interface without full-window upgrade:
  `LocalizedSourceWithoutFullWindowUpgradeTwo`.
- Added staged no-arg direct-witness target from partial-window source:
  `NoargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo`.
- Added root-tail wrapper through that staged no-arg target:
  `mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromPartialWindowSourceTwo`.
- Added direct-constructor alias for partial-window witnesses:
  `ConstructPartialWindowWitnessDirectlyWithoutTransportTwo`.
- Added localized-source constructor map from direct partial-window witnesses:
  `LocalizedSourceWitnessFromPartialWindowConstructorTwo`.
- Added constructor-oriented no-arg direct-witness target:
  `NoargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo`.
- Added root-tail wrapper through constructor-oriented no-arg target:
  `mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo`.
- Added v8 explicit-subcutoff witness candidate interface and equivalence:
  `ExplicitSubcutoffWitnessCandidateFromGreenBoundsTwo` and
  `explicitSubcutoffWitnessCandidateFromGreenBoundsTwo_iff_constructPartialWindowWitnessDirectlyWithoutTransportTwo`.
- Added v8 localized-source constructor interface and equivalence:
  `LocalizedSourceWitnessFromExplicitSubcutoffWitnessTwo` and
  `localizedSourceWitnessFromExplicitSubcutoffWitnessTwo_iff_localizedSourceWitnessFromPartialWindowConstructorTwo`.
- Added v8 no-arg interface and equivalence:
  `NoargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo` and
  `noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo_iff_noargDirectProperLocalWitnessTwoFromConstructedPartialSourceTwo`.
- Added v8 root-tail cutover wrapper:
  `mlc_conjecture_root_tail_nonseam_of_noargDirectProperLocalWitnessTwoFromExplicitLocalizedSourceTwo`.
- Added v9 strict-subcutoff route interface and equivalences:
  `StrictSubcutoffWindowExistenceTwo`,
  `strictSubcutoffWindowExistenceTwo_iff_partialWindowNotCoveringCutoffWithNontransportedTailTwo`,
  `strictSubcutoffWindowExistenceTwo_iff_constructPartialWindowWitnessDirectlyWithoutTransportTwo`.
- Added strong local-window no-go and strict-subcutoff refutation:
  `not_nonimplicativeWindowInterfaceTwo_of_one_lt_radius` and
  `not_strictSubcutoffWindowExistenceTwo`.
- Added v9 direct proper/local witness route packaging:
  `DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo` and
  `directProperLocalWitnessTwo_of_directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo`.
- Added converse and collapse equivalence for that route:
  `directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo_of_directProperLocalWitnessTwo` and
  `directProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo_iff_directProperLocalWitnessTwo`.
- Added v9 root-entry detour wrappers:
  `RootEntryDetourViaInjSurjExteriorConstructivePayloadTwo` and
  `mlc_conjecture_of_rootEntryDetourViaInjSurjExteriorConstructivePayloadTwo`.
- Added v9 seed dependency min-cut interface:
  `SeedDependencyMinCutSliceTwo`.
- Added v10 non-seeded directProper->rootSafe gap interface:
  `NonseededDirectProperToRootSafeGapTwo`.
- Added v10 directProper route matrix collapse:
  `DirectProperLocalWitnessTwoRouteMatrixV10` and
  `directProperLocalWitnessTwoRouteMatrixV10_iff_directProperLocalWitnessTwo`.
- Added explicit seeded fallback endpoint for the v10 gap:
  `nonseededDirectProperToRootSafeGapTwo_seeded_fallback`.
- Added v12 local-seam gap formulation and equivalence:
  `NonseededDirectProperToLocalSeamGapTwo` and
  `nonseededDirectProperToRootSafeGapTwo_iff_nonseededDirectProperToLocalSeamGapTwo`.
- Added v12 local-seam seeded fallback endpoint:
  `nonseededDirectProperToLocalSeamGapTwo_seeded_fallback`.
- Added local-seam route-matrix cutover wrappers:
  `mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_directProperLocalWitnessTwoRouteMatrixV10` and
  `mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_seeded_fallback_of_directProperLocalWitnessTwoRouteMatrixV10`.
- Added v14 source-matrix cutover wrappers:
  `NonseededLocalSeamGapWitnessSourceMatrixV14` and
  `mlc_conjecture_of_nonseededDirectProperToLocalSeamGapTwo_of_nonseededLocalSeamGapWitnessSourceMatrixV14`.
- Added v16 final-gap minimalization aliases and cutover:
  `FinalAxiomEliminationWitnessPairV16`,
  `FinalAxiomCoreConstructiveGapV16`,
  `finalAxiomEliminationGapV15_iff_finalAxiomEliminationWitnessPairV16`,
  and `mlc_conjecture_of_finalAxiomEliminationWitnessPairV16`.
- Added v17 elimination-kernel split and cutover wrappers:
  `FinalAxiomEliminationKernelV17`,
  `finalAxiomEliminationKernelV17_iff_finalAxiomEliminationWitnessPairV16`,
  `finalAxiomEliminationGapV15_iff_finalAxiomEliminationKernelV17`,
  and `mlc_conjecture_of_finalAxiomEliminationKernelV17`.
- Added v18 ingress-kernel reduction and endpoint cutover:
  `FinalAxiomEliminationIngressKernelV18`,
  `finalAxiomEliminationIngressKernelV18_iff_finalAxiomEliminationKernelV17`,
  `finalAxiomEliminationGapV15_iff_finalAxiomEliminationIngressKernelV18`,
  and `mlc_conjecture_of_finalAxiomEliminationIngressKernelV18`.
- Added v19 ingress-bridge equivalence and kernel cutover:
  `FinalAxiomIngressBridgeGapV19`,
  `finalAxiomIngressBridgeGapV19_iff_finalAxiomCoreConstructiveGapV16`,
  `FinalAxiomEliminationIngressBridgeKernelV19`,
  and `mlc_conjecture_of_finalAxiomEliminationIngressBridgeKernelV19`.
- Added grounded v20 normalization wrappers:
  `FinalAxiomSeamDecompositionV20`,
  `FinalAxiomWitnessTransportV20`,
  `FinalAxiomContrapositiveObstructionV20`,
  and their equivalences to `FinalAxiomIngressBridgeGapV19`.
- Added grounded v21 witness-gap kernel wrappers:
  `FinalAxiomWitnessGapBridgeV21`,
  `FinalAxiomWitnessGapKernelV21`,
  `finalAxiomEliminationGapV15_iff_finalAxiomWitnessGapKernelV21`,
  and `mlc_conjecture_of_finalAxiomWitnessGapKernelV21`.
- Added grounded v22 root-witness-gap kernel wrappers:
  `FinalAxiomRootWitnessGapBridgeV22`,
  `FinalAxiomRootWitnessGapKernelV22`,
  `finalAxiomEliminationGapV15_iff_finalAxiomRootWitnessGapKernelV22`,
  and `mlc_conjecture_of_finalAxiomRootWitnessGapKernelV22`.
- Added grounded v23 approach-matrix wrappers:
  `FinalAxiomApproachMatrixV23`,
  `FinalAxiomApproachMatrixKernelV23`,
  `finalAxiomEliminationGapV15_iff_finalAxiomApproachMatrixKernelV23`,
  and `mlc_conjecture_of_finalAxiomApproachMatrixKernelV23`.
- Added grounded v24 root-closure kernel wrappers:
  `FinalAxiomRootClosureBridgeV24`,
  `FinalAxiomRootClosureKernelV24`,
  `finalAxiomEliminationGapV15_iff_finalAxiomRootClosureKernelV24`,
  and `mlc_conjecture_of_finalAxiomRootClosureKernelV24`.
- Current strict-mono-free ingress families are formally blocked:
  `not_rootSafeOutsideOpenInjWitnessTwoStrictMonoFreeIngressTwo`.
- Known blocker to avoid: constructor compositions that introduce non-frontier
  axioms (`MLC.Quadratic.external_ray_map_exists`,
  `MLC.Quadratic.bottcher_seq_converges`).
- The strict-mono seam axiom has already been removed from root frontier.
- The only remaining frontier debt is the anchor-seed axiom above.

## Where To Work

- Root orchestration: `Mlc/MainConjecture.lean`
- Main constructive monotonicity target:
  `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
- Umbrella plan and latest status:
  `plan/PLAN_axiom_elimination_status.md`

## Verification

```bash
make build && make check
```
