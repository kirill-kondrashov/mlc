# PLAN 06: Genuine Böttcher coordinate frontier

**Status:** ACTIVE  
**Root goal:** eliminate `MLC.unifiedGenuineRootKernelTwo`

## Current theorem target

The remaining analytic target is still:

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

This should provide a genuine basin Böttcher coordinate `Φ` through the
candidate / extension-data route already formalized in
`ConstructiveBasinCoordinate.lean`, not through the archived proxy root route.

The theorem-facing reductions are already in place:

1. `ClassicalGlobalBottcherDataFor.toGenuineBottcherCoordinateDataFor`
2. `ClassicalGlobalBottcherDataFor.toGenuineBottcherNearInfinityDataFor`
3. `ClassicalGlobalBottcherDataFor.toGenuineBottcherRouteFor`

So the current work is only to construct the missing classical data.

## Frontier reduction note

After the root reduction to the two remaining non-core frontier axes

1. `MLC.unifiedGenuineRootKernelTwo`
2. `MLC.residualOpenVirtualNearMoleculeAxiom`

the completed/downstream plans were moved to `plan/archive/`. The `plan/`
frontier now consists of the Böttcher-axis package (`PLAN_06`–`PLAN_09`), while
the residual-open renormalization barrier remains an external input not
addressed by a separate plan file in this directory.

## What is now proved

The canonical near-infinity phase is complete for the logarithmic-series
coordinate:

```lean
MLC.logSeriesBottcherApprox c
```

Checked theorems:

1. `nearOneLogCorrection_eq_simple`
2. `LogCorrectionSeriesMajorizedOnExterior.of_large_radius`
3. `LogCorrectionSeriesConvergesOnExterior.of_large_radius`
4. `tendsto_logCorrectionSeries_atInfinity`
5. `tendsto_logSeriesBottcherRatio_atInfinity`
6. `tendsto_logSeriesBottcherApprox_div_atInfinity`
7. `logSeriesBottcherApprox_conj_of_large_radius`
8. `nearOneLogCorrection_differentiableOn_large_radius`
9. `logCorrectionSeries_differentiableOn_large_radius`
10. `logSeriesBottcherApprox_differentiableOn_large_radius`
11. `one_lt_norm_logSeriesBottcherApprox_of_outside_open`
12. `genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox`
13. `genuineBottcherNearInfinityRouteFor_logSeriesBottcherApprox`

Thus the existing canonical interface

```lean
Quadratic.GenuineBottcherNearInfinityDataFor c
```

is now filled without adding axioms.

## Current blocker: basin extension

The remaining problem is to extend `logSeriesBottcherApprox` from the canonical
near-infinity region to the full basin of infinity.

The notebook tracking this Lean frontier is:

```text
notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb
```

The theorem-by-theorem A/B/C unpacking of that unified statement is now kept in

```text
notebooks/plan06_principal_pullback_coherence_companion.ipynb
```

The current principal pullback candidate is:

```lean
principalPullbackLogSeriesBottcher
basinLogSeriesExtensionCandidate
```

Already checked:

1. `exists_iterate_mem_outside_open_of_mem_basin`
2. `basinEscapeTime`
3. `basinEscapeTime_spec`
4. `basinEscapeTime_eq_zero_of_outside_open`
5. `principalPullbackLogSeriesBottcher_eq_near_of_outside_open`
6. `basinLogSeriesExtensionCandidate_extends_near`
7. `rootsOfUnitySet`
8. `pullbackRootSet`
9. `rootsOfUnity_smul_pullbackRootSet`
10. `pullbackRootSet_torsor_transitive`
11. `pullbackRootSet_subset_next_of_sq`
12. `logSeriesBottcherApprox_iterate_succ_eq_sq`
13. `logSeries_pullbackRootSet_subset_next`

The exact remaining Route-A target is:

```lean
PrincipalPullbackCoherentDataFor (2 : ℂ)
```

One field of this target is solved: agreement with the near-infinity coordinate
on the canonical outside-open region. The unsolved fields are:

1. basin exterior-valuedness,
2. basin characterization by exterior norm,
3. basin semiconjugacy,
4. differentiability on the basin,
5. Green-function modulus identity,
6. normalization of the total basin extension.

The main mathematical/formal obstruction is independence of the escape iterate
and coherent branch control for the `2^n`-roots used in the pullback.

## Current reduction seams

The following theorem surfaces isolate the remaining work:

```lean
LogSeriesBasinExtensionDataFor
PrincipalPullbackCoherentDataFor
LogSeriesExteriorInverseBasinExtensionDataFor
MonodromyTrivializingCoverBasinExtensionDataFor
ClassicalGlobalExtensionFromNearInfinityDataFor
```

Checked reductions:

1. `LogSeriesBasinExtensionDataFor.toClassicalGlobalBottcherDataFor`
2. `classicalGlobalBottcherTheoremFor_of_logSeriesBasinExtensionData`
3. `PrincipalPullbackCoherentDataFor.toLogSeriesBasinExtensionDataFor`
4. `classicalGlobalBottcherTheoremFor_of_principalPullbackCoherentData`
5. `classicalGlobalBottcherTheoremFor_of_logSeriesExteriorInverseBasinExtensionData`
6. `MonodromyTrivializingCoverBasinExtensionDataFor.toLogSeriesBasinExtensionDataFor`
7. `classicalGlobalBottcherTheoremFor_of_monodromyTrivializingCoverData`
8. `classicalGlobalBottcherTheoremFor_of_classicalGlobalExtensionFromNearInfinityData`
9. `MLC.MainProof.mlc_conjecture_of_principalPullbackCoherentData_two`

The root-facing cutover theorem

```lean
MLC.MainProof.mlc_conjecture_of_principalPullbackCoherentData_two
```

shows the intended rewiring explicitly: the active PLAN 06 target
`PrincipalPullbackCoherentDataFor (2 : ℂ)`, together with the matching inverse
package for `basinLogSeriesExtensionCandidate (2 : ℂ)`, already lands in the
existing genuine-Böttcher MLC closure chain. Therefore the remaining work is to
internalize the coherent-data and inverse
package inputs without using the proxy-specific `basinExternalRayKernelTwo`
route.

## Next implementation routes

### Route A: coherent pullback branches

Prove:

```lean
PrincipalPullbackCoherentDataFor (2 : ℂ)
```

This means proving the principal pullback candidate is independent of escape
time and is holomorphic locally on the basin.

Current Route-A progress: the finite-level algebraic torsor picture is checked.
Root choices for `w^n = A` are acted on by `n`-th roots of unity, any two
nonzero roots differ by a root of unity, and the Böttcher equation identifies
level-`N` roots as compatible level-`N+1` roots along an escaping orbit. What is
not yet proved is the analytic part: selecting a compatible basepoint
independently of escape time and varying holomorphically on basin neighborhoods.
The monodromy-representation theorem surface is now also formalized through
`PullbackRootMonodromyRepresentation`, `EscapeTimeIndependentPullbackDataFor`,
and `MonodromyTrivialPullbackDataFor`.

The cover strategy suggested by this torsor picture is isolated by
`MonodromyTrivializingCoverBasinExtensionDataFor`: construct the coherent
pullback on a monodromy-trivializing cover, prove same-fiber/deck invariance, and
descend it to the basin. This is a reduction seam, not yet a construction of the
cover data. See `plan/PLAN_07_monodromy_cover_route.md` for the focused
monodromy-cover plan.

### Route B: exterior inverse first

Construct an exterior inverse for `logSeriesBottcherApprox`, then use inverse
dynamics to define the basin extension.

Target seam:

```lean
LogSeriesExteriorInverseBasinExtensionDataFor (2 : ℂ)
```

### Route C: classical extension theorem

Formalize/import the standard theorem extending a local Böttcher coordinate at
superattracting infinity to the full basin.

Target seam:

```lean
ClassicalGlobalExtensionFromNearInfinityDataFor (2 : ℂ)
```

## Immediate next step

Start with Route A. Prove more fields of

```lean
PrincipalPullbackCoherentDataFor (2 : ℂ)
```

in this order:

1. semiconjugacy of `basinLogSeriesExtensionCandidate` on basin points,
2. exterior-valuedness on basin points,
3. Green-function modulus identity,
4. differentiability on the basin.

If coherent root branches block Route A, switch to Route B or Route C.

## Success criterion

PLAN 06 is complete when:

1. `Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)` is proved for the
   genuine coordinate;
2. the matching inverse package proves
   `Quadratic.GenuineBottcherRouteFor (2 : ℂ)`;
3. `MLC.basinExternalRayKernelTwo` is removed from the root path.
