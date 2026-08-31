# GPT-5.4 Result 75 — Parameter external arc constructor

## Prompt executed

`@plan/GPT54_PROMPT_75_PARAMETER_EXTERNAL_ARC_CONSTRUCTOR.md`

## Outcome

I did **not** add a parameter-plane `BoundaryArc` constructor.

Prompt 75 completes as an **honest blocker report**: after auditing the current
parameter-plane external-coordinate / external-ray infrastructure, the repository
still does not contain a non-axiomatic, fully instantiated parameter external
coordinate from which one can build a continuous injective closed-interval arc in
`ℂ \ MandelbrotSet`.

## What I audited

I checked the files most likely to contain a usable parameter-plane source:

- `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherCore.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherProductAnalytic.lean`
- `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`
- `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`
- `Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`
- `Mlc/Quadratic/Complex/Axioms.lean`

## What is available

### 1. Finite boundary-graph topology is ready

`FiniteParapuzzleBoundary.lean` now supplies the abstract target:

- `BoundaryArc` as a continuous injective map `Set.Icc (0 : ℝ) 1 → ℂ`;
- finite unions of carriers;
- open complementary windows;
- nesting/refinement packaging.

So the blocker is **not** finite topology anymore.

### 2. The repo has theorem-facing external-coordinate packages, not an instantiated parameter arc

The strongest positive infrastructure is theorem-facing:

- `GenuineBottcherCoordinateDataFor c φ`
- `GenuineBottcherInversePackageFor c φ`
- `ExternalRayMapDataFor c φ`
- existential cutovers in `GreenFunctionRayInversion.lean`

These establish that **if** a genuine external coordinate `φ` with the right
surjectivity/injectivity payload is available, then one can obtain an external-ray
inverse package.

But Prompt 75 requires an actual proved parameter-plane source theorem, not a
contract of the form “given φ with these properties”.

### 3. The public external-ray existence layer is still axiomatic / seam-dependent

The audit found direct disqualifiers:

- `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean` still declares
  `axiom external_ray_map_exists (c : ℂ) : ExternalRayMapData c`
- `BottcherProductAnalytic.lean` explicitly advertises itself as analytic input for
  the far-exterior true-Böttcher build under the same frontier-axiom route.
- `GreenFunctionRayInversion.lean` contains theorem-facing constructors and also
  remaining seam / axiom markers for ray-monotonicity and cutover.

So the repo does **not** yet contain a standalone proved parameter external
coordinate constructor satisfying Prompt 75.

### 4. The motion-side family files remain ineligible

`BottcherMotion.lean` still contains explicit placeholder hypotheses:

- `homeomorphism_maps_component_hyp : Prop := True`
- `parameter_dynamics_stability_hyp : Prop := True`

and theorem-facing local/global family packages. These are not honest source data
for a parameter external arc under the prompt constraints.

### 5. The outside-open plan is still a plan, not the final constructor needed here

`BottcherOutsidePlan.lean` contains real analytic work and some sorry-free lemmas,
but it also very clearly states the remaining tasks needed to remove the outside
injectivity / external coordinate seam. Its content is about proving the global
outside-open coordinate package, not about a completed parameter-plane arc
constructor from already discharged hypotheses.

In particular, the file itself still presents the needed route as a multi-step
plan toward eliminating the seam.

## First exact missing theorem

The first missing theorem is now sharper than in Result 74:

> a **non-axiomatic parameter-plane external coordinate theorem** producing an
> actual map `Φ : ℂ → ℂ` (or equivalent inverse map) on `ℂ \ MandelbrotSet`
> with enough proved structure to parametrize a closed-interval external arc.

To turn this into a `BoundaryArc`, the repo still needs a theorem package giving
at least the following for one concrete parameter-plane ray/equipotential segment:

1. a proved parameter external coordinate or inverse on the complement of
   `MandelbrotSet`;
2. continuity of the resulting parameter-ray/equipotential map on a closed interval;
3. injectivity on that interval;
4. exterior membership (`γ t ∉ MandelbrotSet` for the parameter values in the arc);
5. any endpoint/level facts needed to attach the arc to a finite boundary graph.

At present, the repository has theorem-facing contracts showing how such data
would be *used*, but not the actual discharged parameter-plane coordinate theorem.

## Why no Lean edit was made

Any attempt to define a parameter external arc now would have had to rely on one of:

- `external_ray_map_exists` or related axiomatic ray-map declarations;
- theorem-facing existential packages without a concrete extracted coordinate;
- placeholder motion/family data;
- a dynamical-plane ray disguised as a parameter-plane arc.

All of these are forbidden by Prompt 75.

## Honest conclusion

Prompt 75 is blocked at the **parameter-plane external coordinate** stage.

Result 73 already provides the finite topological target. Results 74 and 75 now
pinpoint the next genuine missing source theorem:

- Result 74: no honest analytic-to-finite arc constructor yet;
- Result 75: more specifically, no non-axiomatic **parameter-plane external
  coordinate / external-arc theorem** yet.

## Files changed

- Added: `plan/GPT54_RESULT_75_PARAMETER_EXTERNAL_ARC_CONSTRUCTOR.md`

No Lean source files were changed.
