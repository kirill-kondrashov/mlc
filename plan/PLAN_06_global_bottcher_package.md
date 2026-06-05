# PLAN 06: Construct a genuine theorem-facing Böttcher coordinate

**Status:** ACTIVE  
**Root goal:** eliminate `MLC.basinExternalRayKernelTwo`

## What is already settled

The checked root-side chain is already in place:

1. `Quadratic.GenuineBottcherCoordinateDataFor`
2. `Quadratic.GenuineBottcherInversePackageFor`
3. `Quadratic.GenuineBottcherRouteFor`
4. `GenuineBottcherNearInfinityParameterExtensionBridgeTwo`
5. `GenuineBottcherLocalParameterExtensionBridgeTwo`
6. `GenuineBottcherFamilyPromotionBridgeTwo`
7. `GenuineBottcherFamilyBridgeTwo`
8. `GenuineBottcherMotionBridgeTwo`
9. `GenuineBottcherPuzzleBoundaryMotionBridgeTwo`

So the repository no longer lacks a target interface. It lacks the actual
mathematics producing those interfaces.

## What has been ruled out

The current proxy route is dead:

1. `Quadratic.bottcher_map := polar_green_map` is **not** the genuine coordinate.
2. This is formally recorded by
   - `Quadratic.not_bottcherBasinLocalAnalyticityHyp_two`
   - `Quadratic.not_genuineBottcherCoordinateDataFor_bottcherMap_two`
3. Therefore PLAN 06 must construct a **new coordinate object**. It cannot be
   completed by proving one more property of `polar_green_map`.

## Exact missing object

Construct a map

$$
\Phi : U_\infty(2) \to \Omega
$$

with the classical Böttcher properties:

$$
\Phi(f(z)) = \Phi(z)^2,
\qquad
\frac{\Phi(z)}{z}\to 1,
\qquad
|\Phi(z)| = e^{G(z)},
$$

plus:

1. surjectivity onto `Ω`,
2. injectivity on `V = {z : |z| > 4}`.

In code, this means proving `Quadratic.GenuineBottcherRouteFor (2 : ℂ)` for
some **new** `Φ`.

## Short missing-step list

### Step 1. Construct the new near-infinity coordinate

Prove `Quadratic.GenuineBottcherNearInfinityRouteFor (2 : ℂ)` for a new map
`Φ`, not for `Quadratic.bottcher_map`.

Required properties:

1. holomorphicity on `{z : ‖z‖ > R}`,
2. semiconjugacy to squaring there,
3. normalization `Φ(z)/z → 1`,
4. image in `{w : 1 < ‖w‖}`.

### Step 2. Extend that coordinate to the full basin

Promote the near-infinity coordinate to a global theorem-facing coordinate
package:

1. `Quadratic.GenuineBottcherCoordinateDataFor (2 : ℂ) Φ`

This is the main missing theorem. It must be proved for the new `Φ`, not for
the proxy.

### Step 3. Prove the inverse-package consequences

Using the same `Φ`, prove:

1. `Quadratic.GenuineBottcherInversePackageFor (2 : ℂ) Φ`

This is the surjectivity/injectivity part.

### Step 4. Build the parameter-family bridge

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

### Step 5. Finish the root cutover

After Steps 2–4:

1. replace proxy-based root consumption with the genuine route,
2. discharge `MLC.basinExternalRayKernelTwo`,
3. make `make check` report only core axioms.

## Immediate next theorem

The next exact theorem to attack is:

1. a **new** witness for `Quadratic.GenuineBottcherNearInfinityRouteFor (2 : ℂ)`,
   or equivalently the near-infinity half of a new witness for
   `Quadratic.GenuineBottcherRouteFor (2 : ℂ)`.

That is now the clean first blocker. Everything else is downstream.

## Non-goals

PLAN 06 should **not**:

1. keep upgrading `polar_green_map`,
2. redefine `Quadratic.bottcher_map` prematurely,
3. revive old proxy-based inverse statements,
4. reintroduce Lyubich-style root dependencies.

## Success criterion

PLAN 06 is complete when:

1. a theorem proves `Quadratic.GenuineBottcherRouteFor (2 : ℂ)` for a new `Φ`,
2. `MainConjecture.lean` closes from that theorem-facing route,
3. `MLC.basinExternalRayKernelTwo` disappears from the root path.
