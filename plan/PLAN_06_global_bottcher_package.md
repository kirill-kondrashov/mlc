# PLAN 06: Classical global Bottcher theorem package at `c = 2`

**Status:** ACTIVE  
**Frontier role:** live theorem-facing plan for eliminating `MLC.basinExternalRayKernelTwo`  
**Primary formal hooks:** `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`, `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`, `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean`, `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`, `Mlc/MainConjecture.lean`

---

## Root result this plan must deliver

Produce the full theorem-facing package needed to replace the current proxy root
input:

1. a genuine coordinate theorem proving `Quadratic.GenuineBottcherCoordinateDataFor (2 : ℂ) Φ` for some `Φ`,
2. the inverse-package consequences proving `Quadratic.GenuineBottcherInversePackageFor (2 : ℂ) Φ`,
3. the root cutover from proxy-specialized `Quadratic.BasinExternalRayMapDataTwo`
   to the genuine coordinate route,
4. elimination of `MLC.basinExternalRayKernelTwo` so that `make check` reports
   only core axioms.

The already-checked generic bridge means that once items (1) and (2) are proved,
the basin/exterior inverse data package is available without rewriting Step 3.

---

## Exact mathematical target

Let

$$
f(z)=z^2+2,
\qquad
U_\infty=\mathbb{C}\setminus K(f),
\qquad
\Omega=\{w\in\mathbb{C}: |w|>1\},
\qquad
V=\{z\in\mathbb{C}: |z|>4\}.
$$

The package to formalize is:

1. there exists a holomorphic map $$\Phi: U_\infty \to \Omega$$ such that

   $$
   \Phi(f(z))=\Phi(z)^2,
   \qquad
   \lim_{z\to\infty}\frac{\Phi(z)}{z}=1,
   \qquad
   |\Phi(z)|=e^{G(z)};
   $$

2. this same $$\Phi$$ is surjective onto $$\Omega$$;
3. the restriction $$\Phi|_V$$ is injective.

In the codebase this is the bundled theorem-facing target
`Quadratic.GenuineBottcherRouteFor (2 : ℂ)`.

---

## What is already in place

The repository already contains the correct theorem-facing landing surface:

1. `Quadratic.GenuineBottcherCoordinateDataFor`
2. `Quadratic.GenuineBottcherInversePackageFor`
3. `Quadratic.GenuineBottcherRouteFor`
4. `basin_external_ray_map_data_of_genuine_bottcher_inverse_package`
5. `external_ray_map_data_of_genuine_bottcher_inverse_package`

So this plan does **not** need to invent a new root interface. It needs to prove
the missing mathematics and then cut the root over to consume it.

### Checked implementation progress

The root consumer side is now partially prepared:

1. `MainConjecture.lean` exposes
   `GenuineBottcherPuzzleBoundaryMotionBridgeTwo`,
2. `MainConjecture.lean` now also exposes the more concrete seam
   `GenuineBottcherMotionBridgeTwo`, which asks for Bottcher-based motion data
   from the genuine route and converts it to the puzzle-boundary-motion bridge
   through the existing constructor in `BottcherMotion.lean`,
3. `MainConjecture.lean` now also exposes the still-more-precise seam
   `GenuineBottcherFamilyBridgeTwo`, which asks for a local parameter-family
   package from the genuine route and reduces it to the motion bridge,
4. `BottcherMotion.lean` now exposes the theorem-facing family package
   `GenuineBottcherLocalFamilyData` / `GenuineBottcherFamilyHyp` together with
   checked constructors
   `bottcher_motion_hyp_of_genuineBottcherFamily` and
   `puzzle_boundary_motion_hyp_of_genuineBottcherFamily`,
5. `genuineBottcherMotionBridgeTwo_of_familyBridge`,
   `genuineBottcherPuzzleBoundaryMotionBridgeTwo_of_motionBridge`, and
   `mlc_conjecture_of_genuineBottcherMotionBridgeTwo` now make the family →
   motion → puzzle-boundary-motion reduction explicit in checked Lean,
6. `MainConjecture.lean` now isolates the still-closer local step
   `GenuineBottcherLocalParameterExtensionBridgeTwo` and the derived
   depthwise bridge
   `genuineBottcherLocalFamilyBridgeTwo_of_localParameterExtensionBridge`,
   so the route → local-family seam is now explicit too,
7. `ConstructiveBasinCoordinate.lean` now also exposes the explicit Phase-1
   single-parameter package
   `Quadratic.GenuineBottcherNearInfinityDataFor` /
   `Quadratic.GenuineBottcherNearInfinityRouteFor`,
8. `BottcherMotion.lean` now exposes the matching Phase-1 parameter-family
   surfaces
   `Quadratic.GenuineBottcherNearInfinityParameterFamilyData` and
   `Quadratic.GenuineBottcherNearInfinityParameterExtensionData`,
9. `MainConjecture.lean` now isolates the earlier near-infinity seams
   `GenuineBottcherNearInfinityParameterBridgeTwo` and
   `GenuineBottcherNearInfinityParameterExtensionBridgeTwo`,
10. `MainConjecture.lean` now also makes explicit the promotion seam from one
   local parameter-extension package near `2` to the global family hypothesis
   consumed by the motion layer:
   `GenuineBottcherFamilyPromotionBridgeTwo`,
11. `mlc_conjecture_of_genuineBottcherLocalParameterExtensionBridgeTwo` now
   records that local parameter extension is only enough to close the root once
   this promotion seam is supplied as well.
12. `mainPathData_of_genuineBottcherRoute_two` packages the theorem-facing
   Bottcher route into the existing `MainPathData` interface once that bridge is
   available,
13. `mlc_conjecture_of_genuineBottcherRoute_two` closes MLC from the genuine
   Bottcher route, the bridge to puzzle-boundary motion, and the existing
   Track-1/Track-2 package.

So the remaining work is now more exact: the repository no longer lacks the
Phase-5 consumer theorem; it lacks the genuine coordinate theorem itself and the
bridge from that route first to the near-infinity parameter family, then to the
stronger local parameter-extension package feeding
`GenuineBottcherLocalParameterExtensionBridgeTwo`, and finally the promotion of
that one-base-parameter package to the global family hypothesis consumed by the
motion layer.

---

## What is still missing

### A. Genuine coordinate construction

The code still lacks an actual theorem constructing a genuine coordinate `Φ`.
Current `Quadratic.bottcher_map` is still the proxy `polar_green_map`, and the
theorem-facing package is only a `Prop`.

### B. Classical analytic package

The classical global theorem is not internalized yet:

1. a near-infinity Bottcher coordinate on an exterior neighborhood,
2. extension of that coordinate to the full basin of infinity,
3. holomorphicity and nonvanishing on the basin,
4. normalization at infinity,
5. the Green-function modulus identity.

### C. Consequences needed by the root

Even after the coordinate exists, the repo still needs formal proofs that the
same coordinate is:

1. surjective onto $$\Omega$$,
2. injective on $$V$$.

### D. Final root rewiring

Before the root can consume the new local parameter-extension package, the repo
also needs one global-family promotion theorem:

1. from the local package around `2`, produce the global family hypothesis
   `Quadratic.GenuineBottcherFamilyHyp`.

### E. Final root rewiring

`MainConjecture.lean` still routes the root through proxy-specialized objects:

1. `Quadratic.ExternalRayMapData (2 : ℂ)`
2. `Quadratic.BasinExternalRayMapDataTwo`
3. `BottcherSurjOnExterior`
4. `BottcherApproachOneSeqFiberData`

Those surfaces must be cut over so the root consumes the genuine-coordinate
package rather than the proxy `Quadratic.bottcher_map`.

---

## Execution phases

### Phase 1. Local coordinate near infinity

Formalize a genuine near-infinity Bottcher coordinate on some exterior region
$$
\{z : |z| > R\}
$$
with the properties:

1. holomorphicity,
2. semiconjugacy to squaring,
3. normalization
   $$
   \Phi(z)/z \to 1,
   $$
4. image contained in $$\Omega$$.

This is the first mathematical milestone. Without it, all later pullback and
global-extension arguments are blocked.

The theorem-facing Lean surface for this phase is now explicit:

1. `Quadratic.GenuineBottcherNearInfinityDataFor`,
2. `Quadratic.GenuineBottcherNearInfinityRouteFor`,
3. `GenuineBottcherNearInfinityParameterBridgeTwo`.

### Phase 2. Global extension to the basin

Extend the local coordinate to all of $$U_\infty$$ by a pullback / iterate
construction and prove that the extension is well-defined and agrees with the
local coordinate near infinity.

Required outputs:

1. a globally defined map `Φ : ℂ → ℂ` or equivalent theorem-backed object on the basin,
2. semiconjugacy
   $$
   \Phi(f(z))=\Phi(z)^2
   $$
   on the basin,
3. holomorphicity on the basin,
4. nonvanishing on the basin.

On the parameter side, the analogous target is now also explicit:

1. construct `Quadratic.GenuineBottcherNearInfinityParameterFamilyData (2 : ℂ)`,
2. strengthen it to
   `Quadratic.GenuineBottcherNearInfinityParameterExtensionData (2 : ℂ)`,
3. then forget the explicit near-infinity phase via
   `genuineBottcherLocalParameterExtensionBridgeTwo_of_nearInfinityParameterExtensionBridge`.

### Phase 3. Identify the modulus with the Green function

Formalize the uniqueness argument showing that

$$
u(z)=\log |\Phi(z)|
$$

is the Green function on the basin because it is harmonic, satisfies

$$
u(f(z)) = 2u(z),
$$

and obeys

$$
u(z)-\log |z| \to 0
\qquad\text{as } z\to\infty.
$$

This should discharge the modulus clause in
`Quadratic.GenuineBottcherCoordinateDataFor`.

### Phase 4. Prove the inverse-package consequences

Using the genuine coordinate, prove:

1. surjectivity onto $$\Omega$$,
2. injectivity on $$V=\{z : |z|>4\}$$.

These results should be assembled into
`Quadratic.GenuineBottcherInversePackageFor (2 : ℂ) Φ`.

### Phase 5. Assemble and cut over the root

1. Prove `Quadratic.GenuineBottcherRouteFor (2 : ℂ)`.
2. Prove the local-parameter-extension bridge at `2` and the promotion seam
   `GenuineBottcherFamilyPromotionBridgeTwo`.
3. Use the generic bridge in `GreenFunctionRayInversion.lean` to obtain basin and
   exterior inverse data for `Φ`.
4. Replace the proxy-specialized root consumption in `MainConjecture.lean` with
   the theorem-facing genuine-coordinate route.
5. Remove `MLC.basinExternalRayKernelTwo`.

---

## Recommended implementation order

1. Prove a near-infinity coordinate first.
2. Keep the proxy `polar_green_map` and all proxy obstruction theorems intact.
3. Introduce the genuine coordinate in parallel; do **not** redefine
   `Quadratic.bottcher_map` prematurely.
4. Only after `Quadratic.GenuineBottcherRouteFor (2 : ℂ)` is proved should the
   final root be rewired.

This avoids breaking the currently checked proxy-specific contradiction theorems
before the genuine replacement is available.

---

## Explicit non-goals for this plan

This plan should **not**:

1. revive the old Lyubich bridge as a root dependency,
2. revive the false proxy inverse-package statements,
3. treat `PLAN_05_restricted_winding_degree_one.md` as the first live blocker.

`PLAN_05` becomes relevant only after the genuine coordinate exists and if the
project later wants an auxiliary degree-one proof of the outside-open
injectivity consequence.

---

## Success criterion

This plan succeeds when all of the following are true:

1. there is a theorem proving `Quadratic.GenuineBottcherRouteFor (2 : ℂ)`,
2. `MainConjecture.lean` closes `MLC.mlc_conjecture` from that theorem-facing
   route rather than from `MLC.basinExternalRayKernelTwo`,
3. `make check` reports no non-core project axioms on the root path.
