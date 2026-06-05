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
