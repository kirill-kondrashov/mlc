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
   **active best route**.
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
3. **Candidate 3: pull back a near-infinity coordinate to the basin** —
   **blocked downstream of Candidate 2**.
   This only becomes meaningful after Candidate 2 produces a genuine holomorphic
   near-infinity coordinate.
4. **Candidate 4: Riemann-map / uniformization route** — **blocked**.
   No usable Riemann-map / uniformization theorem support was found.
5. **Candidate 5: Green + harmonic conjugate route** — **blocked**.
   No usable global harmonic-conjugate package was found.
6. **Candidate 6: functional-equation / fixed-point or Laurent-series route** —
   **lower priority / effectively blocked**.
   General analytic tools exist, but nothing close to a ready-made local
   Böttcher construction; Candidate 2 has much stronger existing support.

So the honest next implementation target is now:

1. build the near-infinity coordinate by Candidate 2 on one explicit exterior
   region with a coherent branch choice;
2. upgrade the current **sectorial** candidate package to one honest
   near-infinity map on a fixed simply connected exterior region;
3. only then attempt the basin extension step for
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
