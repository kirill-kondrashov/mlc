# GPT-5.4 Result 74 — Instantiate quadratic parapuzzle boundaries

## Prompt executed

`@plan/GPT54_PROMPT_74_INSTANTIATE_QUADRATIC_PARAPUZZLE_BOUNDARIES.md`

## Outcome

I did **not** add a quadratic instantiation of
`Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`.

Prompt 74 completes as an **honest blocker report**: the repository now has a
checked finite embedded boundary-graph foundation (Result 73), but it does not
yet have a genuinely proved quadratic source object that can be turned into those
arcs without smuggling in unproved landing/continuity/injectivity facts.

## What I audited

I re-checked the strongest candidate source files:

- `Mlc/Quadratic/Complex/Bottcher/BottcherRayMap.lean`
- `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`
- `Mlc/Quadratic/Complex/ParaPuzzle.lean`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean`

## What is actually available

### 1. Parameter puzzle pieces exist only as open sets

`ParaPuzzlePieceAt c n` is currently defined as a translated dynamical puzzle piece:

```lean
{c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
```

and `ParaPuzzleBasis.lean` proves useful set-theoretic facts about these pieces:

- openness;
- boundedness;
- closure containment in Green sublevel sets;
- nesting;
- basis-style consequences under a separate shrink hypothesis.

But this is still **piece-level** information, not a finite explicit boundary graph.

### 2. Ray/exterior map material is still theorem-facing and partial

`BottcherRayMap.lean` proves continuity of `external_ray_map c` on the exterior
**assuming** strong hypotheses on `proxy_bottcher_map c`:

- continuity;
- injectivity;
- openness / open embedding;
- surjectivity onto the exterior.

So this is not yet a ready-made constructor for a concrete boundary arc.

### 3. `GreenFunctionRayInversion.lean` builds exterior inverse packages, not finite parapuzzle arcs

The strongest proved objects there are basin/exterior inverse packages for a
Böttcher-like coordinate, including a `c = 2` specialization and theorem-facing
constructors from coordinate/inverse assumptions.

This is valuable infrastructure, but it still does **not** produce:

- a parameter-side finite family of ray segments/equipotential arcs;
- continuity on a closed interval suitable for `BoundaryArc`;
- injectivity on that interval;
- endpoint landing/compatibility theorems;
- no-crossing/incidence/refinement statements.

### 4. `BottcherMotion.lean` remains explicitly placeholder-heavy

The central motion-side file still contains non-source hypotheses such as:

- `homeomorphism_maps_component_hyp : Prop := True`
- `parameter_dynamics_stability_hyp : Prop := True`

and theorem-facing packages like `GenuineBottcherLocalFamilyData` whose fields
state the desired compatibility with puzzle boundaries. These are contracts, not
instantiated finite boundary geometry.

So it would be dishonest to treat them as actual quadratic parapuzzle boundary data.

## First exact missing theorem

The first missing ingredient is **not** abstract finite topology anymore; Result 73
already supplied that. The first missing ingredient is now a genuine **analytic-to-
finite-arc constructor** of one of the following forms:

1. a proved continuous injective map `Set.Icc (0:ℝ) 1 → ℂ` parametrizing a
   finite external ray segment or equipotential arc for a quadratic parameter; or
2. a proved finite family of such maps with endpoint/incidence compatibility and
   refinement behavior.

Concretely, what is missing is a theorem package establishing enough of:

- continuous extension of a chosen ray/equipotential parametrization to a closed interval;
- injectivity on that interval;
- endpoint description / landing;
- compatibility of multiple arcs into a finite graph;
- refinement/nesting under depth increase.

Without one of those, there is no honest way to instantiate `BoundaryArc` with
actual quadratic parapuzzle geometry.

## Why I did not add a “partial combinatorial layer”

The prompt allowed a partial finite combinatorial layer if that layer were
**genuinely proved**. But after audit, the repo does not yet contain a concrete,
finite, already-verified parameter-side combinatorial object of rays/equipotentials
that can be packaged independently of the missing analytic extension facts.

Adding a structure of “angles + expected endpoints + expected incidence” would only
restate the desired geometry in new fields, which the prompt explicitly forbids.

## Honest conclusion

Prompt 74 is therefore blocked at the **first analytic/geometric instantiation step**:

> the repository still lacks a checked theorem turning quadratic external-ray /
> equipotential data into concrete continuous injective closed-interval arcs with
> endpoint control suitable for `BoundaryArc`.

Once that exists, the Result 73 finite boundary-graph foundation is ready to absorb it.

## Files changed

- Added: `plan/GPT54_RESULT_74_INSTANTIATE_QUADRATIC_PARAPUZZLE_BOUNDARIES.md`

No Lean source files were changed.
