# PLAN 06: Construct a genuine theorem-facing Böttcher coordinate

**Status:** ACTIVE  
**Root goal:** eliminate `MLC.basinExternalRayKernelTwo`

## What is already settled

The checked root-side chain is already in place:

1. `Quadratic.GenuineBottcherCoordinateDataFor`
2. `Quadratic.GenuineBottcherInversePackageFor`
3. `Quadratic.GenuineBottcherRouteFor`
4. `Quadratic.ClassicalGlobalBottcherTheoremFor`
5. `GenuineBottcherNearInfinityParameterExtensionBridgeTwo`
6. `GenuineBottcherLocalParameterExtensionBridgeTwo`
7. `GenuineBottcherFamilyPromotionBridgeTwo`
8. `GenuineBottcherFamilyBridgeTwo`
9. `GenuineBottcherMotionBridgeTwo`
10. `GenuineBottcherPuzzleBoundaryMotionBridgeTwo`

So the repository no longer lacks a target interface. It lacks the actual
mathematics producing those interfaces.

## What has been ruled out

The current proxy route is dead:

1. `Quadratic.proxy_bottcher_map := polar_green_map` is **not** the genuine coordinate.
2. This is formally recorded by
   - `Quadratic.not_bottcherBasinLocalAnalyticityHyp_two`
   - `Quadratic.not_genuineBottcherCoordinateDataFor_bottcherMap_two`
3. Therefore PLAN 06 must construct a **new coordinate object**. It cannot be
   completed by proving one more property of `polar_green_map`.

## Exact missing object

Internalize the **classical global theorem** first, before the inverse package:

1. `Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)`

Its content is:

1. a near-infinity Böttcher coordinate on some exterior neighborhood,
2. an extension of that coordinate to the full basin of infinity,
3. holomorphicity and nonvanishing on the basin,
4. normalization at infinity,
5. the Green-function modulus identity on the basin.

Only after that comes the separate inverse package:

1. surjectivity onto `Ω`,
2. injectivity on `V = {z : |z| > 4}`.

## Short missing-step list

### Step 1. Prove the classical global theorem

Prove `Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)` for a **new**
coordinate object, not for `Quadratic.proxy_bottcher_map`.

This single theorem must now internalize the classical analytic core:

1. near-infinity construction on an exterior region,
2. extension to the full basin,
3. basin holomorphicity,
4. basin nonvanishing / exterior-valuedness,
5. normalization at infinity,
6. Green-function modulus identity.

The code already contains the checked reduction

1. `ClassicalGlobalBottcherDataFor.toGenuineBottcherCoordinateDataFor`

so once Step 1 is proved, the theorem-facing coordinate package follows.
Right now this is the **stuck point**: the interface is in Lean, but the repo
still does not construct a witness of
`Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)`.

More precisely, the current code only supplies proxy-side partial results:

1. `proxy_bottcher_map_differentiableOn_open` and
   `proxy_bottcher_map_analyticOnNhd_open` work only on open sets
   `U ⊆ slit_orbit c ∩ basin_of_infinity c`;
2. `slit_orbit` already fails at the basin point `0` when `c = 2`;
3. `BottcherOutsidePlan.lean` explicitly notes that the strong normalization
   `Tendsto (fun z => proxy_bottcher_map c z / z) atInfinity (𝓝 1)` is **not
   expected** for the current explicit proxy.

So replacing `proxy_bottcher_map` by definition is not the next step. The next
step is proving a different global coordinate theorem and only then cutting over
the consumers.

### Step 2. Prove the inverse-package consequences

Using the same global `Φ`, prove:

1. `Quadratic.GenuineBottcherInversePackageFor (2 : ℂ) Φ`

Then the checked reduction

1. `ClassicalGlobalBottcherDataFor.toGenuineBottcherRouteFor`

recovers `Quadratic.GenuineBottcherRouteFor (2 : ℂ)`.

### Step 3. Build the parameter-family bridge

From the single-parameter route, construct the near-infinity parameter package:

1. `GenuineBottcherNearInfinityParameterExtensionBridgeTwo`

The checked reductions already provide:

$$
\text{near-infinity extension}
\Rightarrow
\text{local parameter extension}
\Rightarrow
\text{family/motion chain}.
$$

### Step 4. Finish the root cutover

After Steps 1–3:

1. replace proxy-based root consumption with the genuine route,
2. discharge `MLC.basinExternalRayKernelTwo`,
3. make `make check` report only core axioms.

## Immediate next theorem

The next exact theorem to attack is now:

1. `Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)`

This is the clean analytic blocker. The inverse package and all parameter-family
steps are downstream of it. At present, this theorem is **not proved** in the
repository.

## Candidate loop status

The candidate constructions have now been checked in order against the current
repo/library support.

1. **Candidate 1: local Böttcher at infinity via inversion** — **blocked**.
   No packaged local Böttcher theorem near a superattracting fixed point was
   found in the current repo or imported libraries.
2. **Candidate 2: coherently-branched root-limit on one exterior domain** —
   **blocked as a direct witness for the current near-infinity interface**.
   Existing support already includes:
   - slit-plane and rotated-slit branch domains in
     `InverseBranchQuadratic.lean`,
   - square-root right inverses on those domains,
   - `analytic_root_aux` / `one_add_cpow` branch machinery,
   - near-infinity asymptotic control in `BottcherOutsidePlan.lean`.
   Also, `no_square_root_right_inverse_on_exterior` shows this must be done on a
   simply connected exterior region, not on the full exterior at once.
   The current constructed objects are now:
   - `rootSeqRatioCandidate`
   - `sectorialBottcherApprox`
   - `tendsto_sectorialBottcherApprox_div_atInfinity_in_sector`
   - `eventuallyEq_bottcher_root_seq_ratio_rootSeqRatioCandidate_in_sector`
   - `eventuallyEq_bottcher_root_seq_sectorialBottcherApprox_in_sector`
   These give an explicit sectorial coherent-branch candidate and identify it
   with the existing finite root approximants on the matching sector filter.
   In particular, the sectorial candidate now carries the direct normalization
   statement `sectorialBottcherApprox c N z / z → 1` on
   `atInfinity ⊓ 𝓟 (arg_sector N)`.
   The current obstruction is now formal:
   - `not_exterior_subset_arg_sector`
   proves that no `arg_sector N` contains a full exterior neighborhood
   `{z | R < ‖z‖}`.
   Hence the present sectorial Candidate-2 package cannot directly fill
   `ClassicalGlobalBottcherDataFor.nearPhi`, whose domain is an honest exterior
   neighborhood. Completing this route would require a new gluing/patching
   theorem across sectors, not just one more sector estimate.
3. **Candidate 3: pull back a near-infinity coordinate to the basin** —
   **blocked downstream of Candidate 7**.
   This only becomes meaningful after the correction-product route, or another
   route, produces a genuine holomorphic near-infinity coordinate.
4. **Candidate 4: Riemann-map / uniformization route** — **blocked**.
   No usable Riemann-map / uniformization theorem support was found.
5. **Candidate 5: Green + harmonic conjugate route** — **blocked**.
   No usable global harmonic-conjugate package was found.
6. **Candidate 6: functional-equation / fixed-point or Laurent-series route** —
   **superseded by Candidate 7 below**.
   The old sector branch attempt exposed that the next route must avoid taking
   roots of the leading `z^(2^n)` term directly.
7. **Candidate 7: near-one correction product at infinity** —
   **partially constructed; blocked at the convergence/tail-estimate seam**.
   This refactors the root construction as
   `z` times a product of correction factors tending to `1`, so fractional
   powers are applied only near the slit-plane-safe point `1` and no shrinking
   `arg_sector N` condition is imposed on `z`.
   Checked finite-stage objects now exist in `BottcherOutsidePlan.lean`:
   - `nearOneCorrectionFactor`
   - `finiteProductBottcherRatio`
   - `finiteProductBottcherApprox`
   - `correctionProductBottcherRatio`
   - `correctionProductBottcherApprox`
   - `tendsto_nearOneCorrectionFactor_atInfinity`
   - `tendsto_finiteProductBottcherRatio_atInfinity`
   - `tendsto_finiteProductBottcherApprox_div_atInfinity`
   - `CorrectionProductConvergesOnExterior`
   - `CorrectionProductConvergesOnExterior.tendsto_finiteProductRatio`
   - `tendsto_correctionProductBottcherApprox_div_atInfinity_of_ratio`
   These prove full-filter normalization for every finite product approximation,
   define the ordered conditional infinite-product candidate, and identify the
   exact convergence seam. The missing theorem is still a quantitative
   summable/uniform tail estimate proving locally uniform convergence of the
   products on some `{z | R < ‖z‖}`. Without that, holomorphicity of the limit,
   normalization of the infinite product, and the Böttcher conjugacy identity
   cannot be discharged.
8. **Candidate 8: logarithmic near-one series** —
   **partially constructed; blocked at the additive majorant seam**.
   This is the additive version of Candidate 7:
   \[
     \Phi(z)=z\cdot\exp\left(\sum_{n\ge0} 2^{-(n+1)}
       \Log\left(1+\frac{c}{f_c^n(z)^2}\right)\right).
   \]
   It keeps the same near-one branch safety, but replaces infinite-product
   convergence by locally uniform convergence of a complex-valued series. This
   is more formalizable in Lean because `Summable`, locally uniform series, and
   differentiability of locally uniform limits are already better developed than
   the multiplicative product estimates needed by Candidate 7.
   Checked objects now exist in `BottcherOutsidePlan.lean`:
   - `nearOneLogCorrection`
   - `finiteLogCorrectionSum`
   - `finiteLogSeriesBottcherRatio`
   - `finiteLogSeriesBottcherApprox`
   - `logCorrectionSeries`
   - `logSeriesBottcherRatio`
   - `logSeriesBottcherApprox`
   - `tendsto_nearOneLogCorrection_atInfinity`
   - `tendsto_finiteLogCorrectionSum_atInfinity`
   - `tendsto_finiteLogSeriesBottcherRatio_atInfinity`
   - `tendsto_finiteLogSeriesBottcherApprox_div_atInfinity`
   - `LogCorrectionSeriesConvergesOnExterior`
   - `LogCorrectionSeriesMajorizedOnExterior`
   - `LogCorrectionSeriesConvergesOnExterior.of_majorant`
   - `LogCorrectionSeriesConvergesOnExterior.tendsto_finiteLogCorrectionSum`
   - `tendsto_logSeriesBottcherApprox_div_atInfinity_of_ratio`
   Thus Candidate 8 now has a concrete infinite coordinate candidate and a
   checked Weierstrass-test bridge. The remaining blocker is proving
   `LogCorrectionSeriesMajorizedOnExterior c R` for some large `R`: a summable
   uniform majorant for
   `‖nearOneLogCorrection c n z‖` on `{z | R < ‖z‖}`. The current repository has
   qualitative escape and linear/monotone exterior growth lemmas, but not yet
   the double-exponential exterior lower bound and complex-log near-one estimate
   needed to discharge this majorant.
9. **Candidate 9: Laurent/fixed-point local Böttcher construction at infinity** —
   **partially formalized; blocked at the local superattracting theorem**.
   Work in the coordinate `w = 1/z` near `w = 0` and construct the normalized
   local Böttcher function by a power-series or contraction/fixed-point theorem
   for the functional equation. This avoids choosing iterated roots and avoids
   the global product/series tail, but it requires formalizing a local analytic
   fixed-point/power-series convergence theorem that is not currently packaged
   in the repo.
   Checked objects now exist in `ConstructiveBasinCoordinate.lean`:
   - `invertedQuadraticMap`
   - `infinityCoordinateOfInvertedLocal`
   - `invertedQuadraticMap_inv_eq_inv_quadratic`
   - `InvertedLocalBottcherDataFor`
   - `InvertedLocalBottcherDataFor.nearInfinityPhi`
   - `InvertedLocalBottcherDataFor.toGenuineBottcherNearInfinityDataFor`
   - `InvertedLocalBottcherTheoremFor`
   - `genuineBottcherNearInfinityRouteFor_of_invertedLocalBottcherTheoremFor`
   - `invertedQuadraticMap_ne_sq_of_mul_ne_zero`
   - `invertedQuadraticMap_half_ne_half_sq_two`
   - `not_exists_linear_invertedLocalConj_two`
   Thus Candidate 9 is not disproved: its pullback algebra, exterior-valuedness,
   conjugacy, differentiability, and normalization reduction are checked.
   The naive identity coordinate `ψ(w)=w` and every nonzero scalar-linear
   coordinate `ψ(w)=a w` are formally ruled out, so Candidate 9 cannot be
   completed by just using a linear Laurent coordinate.
   The remaining blocker is precisely the local theorem constructing
   `InvertedLocalBottcherDataFor c`, i.e. the local Böttcher theorem for
   `w ↦ w^2/(1+c w^2)` near the superattracting fixed point `0`.
10. **Candidate 10: explicit majorant proof for Candidate 8** —
   **completed for the convergence seam**.
   Rather than opening a new analytic fixed-point formalization, this route proves
   the exact estimates needed by `LogCorrectionSeriesMajorizedOnExterior`.
   Checked objects now exist in `BottcherOutsidePlan.lean`:
   - `nearOneLogCorrection_eq_simple`
   - `exteriorGrowthLower`
   - `exteriorGrowthLower_nonneg`
   - `exteriorGrowthLower_le_norm_iterate`
   - `LogCorrectionSeriesMajorizedOnExterior.of_large_radius`
   - `LogCorrectionSeriesConvergesOnExterior.of_large_radius`
   Thus the Candidate-8 M-test/convergence seam is discharged on any exterior
   radius `R` with `‖c‖ + 2 ≤ R`.
11. **Candidate 11: log-series-to-Böttcher package bridge** —
   **new active route**.
   Starting from `LogCorrectionSeriesConvergesOnExterior.of_large_radius`, prove
   that `logSeriesBottcherApprox` is a genuine near-infinity Böttcher coordinate:
   1. `logCorrectionSeries c z → 0` as `z → ∞`,
   2. hence `logSeriesBottcherApprox c z / z → 1`,
   3. locally uniform convergence plus differentiability of finite log sums gives
      differentiability on the exterior region,
   4. the shifted logarithmic series gives the conjugacy
      `Φ(f_c z) = (Φ z)^2`,
   5. exterior-valuedness follows from normalization after possibly enlarging
      the radius.
   Current checked progress:
   - `tendsto_logCorrectionSeries_atInfinity`
   - `tendsto_logSeriesBottcherRatio_atInfinity`
   - `tendsto_logSeriesBottcherApprox_div_atInfinity`
   - `eventually_one_lt_norm_logSeriesBottcherApprox_atInfinity`
   - `exists_radius_one_lt_norm_logSeriesBottcherApprox`
   Thus normalization and eventual exterior-valuedness are proved. The remaining
   blockers are:
   - the shifted-series identity needed for
     `logSeriesBottcherApprox c (quadratic_map c z) =
      (logSeriesBottcherApprox c z)^2`;
   - differentiability of the infinite log-series coordinate on an exterior
     region, which requires packaging differentiability of each log correction
     term and applying the locally uniform series theorem.

So the honest next implementation target is now:

1. prove the normalization of `logSeriesBottcherApprox` at infinity from the
   now-checked majorant/convergence seam;
2. prove the logarithmic shift identity and derive Böttcher conjugacy;
3. package differentiability and exterior-valuedness on a sufficiently large
   exterior region;
4. only then attempt the basin extension step for
   `Quadratic.ClassicalGlobalBottcherTheoremFor`.

## Non-goals

PLAN 06 should **not**:

1. keep upgrading `polar_green_map`,
2. redefine `Quadratic.proxy_bottcher_map` prematurely,
3. revive old proxy-based inverse statements,
4. collapse the classical theorem and inverse package into one opaque target,
5. reintroduce Lyubich-style root dependencies.

## Success criterion

PLAN 06 is complete when:

1. a theorem proves `Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)` for a
   new `Φ`,
2. the matching inverse package proves `Quadratic.GenuineBottcherRouteFor (2 : ℂ)`,
3. `MainConjecture.lean` closes from that theorem-facing route,
4. `MLC.basinExternalRayKernelTwo` disappears from the root path.
