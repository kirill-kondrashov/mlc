# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository contains a compact Lean 4 formalization of the Mandelbrot
local-connectivity conjecture with an explicit repaired root input and no
replacement axioms.

## Target

For $c,z\in\mathbb C$, write $f_c(z)=z^2+c$ and let $\mathcal M$ be the
Mandelbrot set. The sound repaired root theorem is categorical:

```lean
MLC.Categorical.categorical_mlc_conjecture :
  MLC.RootInput →
    MLC.Categorical.MLCConjecture
```

Here `MLC.Categorical.MLCConjecture` is local connectedness of the object
`TopCat.of MLC.mandelbrotSet`. The compatibility theorem

```lean
MLC.mlc_conjecture :
  MLC.RootInput →
    LocallyConnectedSpace MLC.mandelbrotSet
```

is equivalent to it by `MLC.Categorical.mlc_conjecture_iff_categorical`.

The frozen parameter neighborhoods
$A_n(c)=\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}$ are a deliberately simplified
Green-sublevel model, not graph-cut Yoccoz parapuzzle pieces. They do not
shrink to $c$: `iInter_green_sublevel_translate_eq_translate_filledJulia`
identifies their intersection with $c+K_c$, and
`Mlc/ModelRegression.lean` records the resulting non-shrinking theorem. The
universal Green-sublevel/Mandelbrot intersection axiom is therefore removed
from the supported theory after the counterexample in
[`refs/green_sublevel_intersection_categorical_counterexample.md`](refs/green_sublevel_intersection_categorical_counterexample.md).

The replacement uses connected components of metric balls together with the
finite outer approximations `Categorical.Mandelbrot.outerOrbitSet`. The
theorem `ParameterComponent.mandelbrot_locallyConnected_of_uniformOuterBuffer`
proves local connectedness from the explicit
`ParameterComponent.MandelbrotUniformOuterBuffer` hypothesis. No inhabitant
of that hypothesis is currently claimed.

The refutation is now also formalized: `MLC.not_greenSublevelIntersectionCategoricalData`
uses the exact 298-cell interval certificate from the counterexample reference
and depends only on Lean foundations. Thus the old frontier is explicitly
known to be incompatible with the repository's frozen definitions.

## Checked Lean state

The repaired root theorems are `sorry`-free. Their theorem argument is the
explicit `MLC.RootInput` proposition; it is not hidden as a project axiom. The
formal counterexample proves that the old Green-intersection frontier is
incompatible with the repository's definitions.

The repaired route and counterexample use only Lean foundations:

```text
Quot.sound
propext
Classical.choice
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
```

The checker then reports that the root theorems require `MLC.RootInput` and
audits the foundation-only counterexample.

## Proved core

- $K_c$ is connected for $c\in\mathcal M$.
- The dynamical Green sublevels $\{z:G_c(z)<2^{-n}\}$ are connected.
- Translation identifies the frozen parameter pieces with those sublevels.
- The subset stratum of $T_n(c)$ is connected without an axiom.
- Components of metric balls are connected, and the component/outer-buffer
  reduction is proved without a project-level frontier axiom.
- The simplified Green-sublevel tower itself is not a faithful shrinking
  Yoccoz tower.
- Retained glue forwards to standard Mathlib/Yoccoz APIs, including
  `locallyConnectedSpace_iff_connected_subsets`, `Set.image_iInter`,
  `integral_biUnion_finset`, `modulus`, and `groetzsch_criterion`.

`check_axioms.lean` checks both repaired root theorems and the counterexample
against the foundational frontier. The complete checked Lean source pass is
warning-free.

## Categorical migration

The root reformulation uses `TopCat` and its over-category over the ambient
parameter plane:

- `Mlc/CategoricalTopologicalApproximation.lean` treats approximations as
  objects of `Over (TopCat.of ℂ)`, the over-category over $\mathbb C$,
  intersections as categorical pullbacks, and
  nested approximations as opposite-indexed diagrams with a universal limit.
- `Mlc/CategoricalRoot.lean` defines the categorical MLC object, the
  `RootInput` structure, the repaired categorical root theorem, and its
  equivalence with the compatibility target.
- `Mlc/CategoricalMandelbrot.lean` gives the boundary, interior, ordinary
  subspace presentations, a deliberately finer boundary topology, the
  parameter-puzzle tower, and a two-sided orbit approximation of `M`.
- `Mlc/CategoricalResidual.lean` presents the two residual renormalization
  inputs as a binary product in `Type`.
- `Mlc/ParameterComponentApproximation.lean` defines dyadic metric-ball
  components, proves the component/outer-buffer local-connectedness
  reduction, and instantiates it for the finite outer critical-orbit
  approximations of the Mandelbrot set.
- `Mlc/ModelRegression.lean` records that the frozen Green tower does not
  shrink to its center and that the imported Gaussian weighted-area proxy is
  summable.
- `Mlc/GreenSublevelIntersectionCounterexample.lean` formalizes the finite
  interval certificate, the horizontal separation argument, and the
  foundation-only negation of the frozen Green-intersection datum.
- `Mlc/EfimovCategoricalBridge.lean` records an honest conditional
  Efimov/Pacman interface: rigid monoidal tower levels with adjunctions,
  strong Mittag--Leffler data, a graded additive `K_n` shadow with an explicit
  limit-comparison input, compatible `TopCat` realization, and a
  space-holomorphic carving bridge whose source is the proved translated Green
  sublevel rather than an arbitrary connected set. It also contains a
  finite-etale degree-zero component probe
  `FiniteEtaleKZeroProbe S := LocallyConstant S Bool`. The proved equivalence
  `IsConnected S ↔ FiniteEtaleKZeroProbeTrivial S` (for nonempty `S`) gives an
  axiom-free `K₀`-like connectedness test. Finite-stage descent and relative
  restriction-surjectivity are exposed as explicit Efimov-inspired inputs;
  the latter is proved equivalent to the straddling connectedness statement,
  so it refines the frontier without disguising or adding an axiom.
  The `DouadyHubbardYoccozCategoricalCarvingData` structure reformulates the
  parameter--dynamical theorem as a surjective morphism in `TopCat` from the
  connected Green-sublevel source to the pullback target, and
  `greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz` proves
  that this categorical theorem implies the frontier.

The categorical presentations are logically equivalent to the two existing
frontier inputs; they do not discharge either open mathematical problem. A
`K_n`-theoretic layer is represented only by the explicit graded additive
interface in `Mlc/EfimovCategoricalBridge.lean`; Mathlib does not currently
provide the stable infinity-categorical or algebraic `K`-theory machinery
needed to instantiate it.

## Combinatorial limits, classification, and flow interfaces

The implementation of
[`refs/mandelbrot_combinatorial_limit_and_flow_program.md`](refs/mandelbrot_combinatorial_limit_and_flow_program.md)
is split into proved certificate interfaces and explicitly retained
obligations:

- `Mlc/CertifiedOrbitApproximation.lean` defines finite compact-cell outer
  stages and proves their nested compact limit is the Mandelbrot set. The
  exact finite-orbit stages are supplied as a verified one-cell baseline;
  cubical, interval, or CAD cell generators must still provide their
  certificate fields.
- `Mlc/CertifiedTrappingRegions.lean` defines rational-box forward-trapping
  certificates and proves that certified inner boxes lie in the Mandelbrot
  set. `InnerDensity` remains an explicit proposition and is not assumed.
- `Mlc/ParameterClassification.lean` proves an exhaustive priority
  classification interface, including first escape times outside the
  Mandelbrot set. The residual class is retained rather than declared empty.
- `Mlc/ParameterAddressSpace.lean` proves compact nested address
  intersections and singleton uniqueness under a vanishing-diameter
  certificate. Address coverage remains a separate obligation.
- `Mlc/FiniteComponentCriterion.lean` proves that finite local-piece cover
  certificates imply the existing `MandelbrotUniformOuterBuffer` root input.
- `Mlc/FlowInterfaces.lean` formalizes uniform-limit parametrizations and
  terminal radial-extension data. These are theorem inputs only; no terminal
  extension or flow-to-MLC theorem is asserted.

These modules introduce no project-level axioms and are imported by the
public `Mlc.lean` root.

The same `CategoricalMandelbrot` module contains a nontrivial two-sided
approximation envelope:

- `innerOrbitSet N` consists of parameters whose entire critical orbit is
  bounded by the single natural witness `N`; these sets increase with `N` and
  satisfy `⋃ N, innerOrbitSet N = M` directly from `boundedOrbit`.
- `outerOrbitSet N` consists of parameters in the universal disk
  `‖c‖ ≤ 2` whose first `N` critical-orbit observations stay within radius
  `2`; these compact sets decrease with `N` and satisfy
  `⋂ N, outerOrbitSet N = M` using `Molecule.mandelbrot_eq_inter`.
- `innerOrbitApproximation N` and `outerOrbitApproximation N` are their
  objects in `Over (TopCat.of ℂ)`. For every `N`, explicit morphisms give the
  sandwich `innerOrbitApproximation N → M → outerOrbitApproximation N`.
- `TwoSidedSetApproximation.isConnected_of_inner` and
  `TwoSidedSetApproximation.isPreconnected_of_outer` expose the two genuine
  finite-stage routes: connected increasing inner stages, or compact
  preconnected decreasing outer stages. The repository does not assume either
  finite-stage property, so these are proof interfaces rather than hidden
  replacements for the frontier axiom.

The limit identities are proved rather than postulated:
`iUnion_innerOrbitSet_eq_set` and `iInter_outerOrbitSet_eq_set`. This is a
separate orbit-envelope layer from the simplified Green-sublevel tower: it
provides finite dynamical observations on the outer side and finite uniform
bound witnesses on the inner side, so later phase--parameter or K-theoretic
arguments can be attached to a genuine two-sided system.

The finite-etale probe is intentionally a topological shadow rather than a
claim that Mathlib already contains continuous algebraic `K`-theory. It
detects exactly the obstruction relevant here: a nontrivial locally constant
two-valued function is a clopen decomposition. The target-specific theorem
`greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroExcisionData`
therefore gives a precise relative-localizing-invariant reformulation of the
remaining parameter-puzzle axiom. The stronger categorical statement
`greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroPullbackData`
identifies the same condition directly on the pullback in `TopCat / ℂ`.
Efimov's results motivate the descent and excision interfaces, but do not
prove their Mandelbrot realization fields.

The categorical Douady--Hubbard/Yoccoz theorem is a proved reduction, not an
unproved assertion: a surjective `TopCat` morphism from the connected
translated Green sublevel yields connectedness of the pullback by the
standard connected-image theorem. The existence of that morphism for the
actual Mandelbrot intersection remains the analytic parameter--dynamical
content. Since the current source is a full Green sublevel rather than a
graph-cut parapuzzle, the repository does not claim that this existence field
is supplied by the classical Yoccoz theorem.

The ten-iteration proof search for the remaining frontier is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts.md`](refs/green_sublevel_intersection_categorical_proof_attempts.md).
It formalizes the successful connected-image reduction and separately records
why factor connectedness, outer/inner limits, Böttcher coordinates, classical
Yoccoz parapuzzles, and finite-etale `K₀` descent do not by themselves supply
the missing carving existence theorem.

A second ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round2.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round2.md).
It tests continuum separation, proper maps, straightening, external-ray
graphs, harmonic measure, renormalization inverse limits, prime ends,
Alexander duality, finite-stage regular epimorphisms, and axiom-minimality.
The result is the same: only the explicit connected-surjective carving
implication is formalized; its existence remains the frontier.

A third ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round3.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round3.md).
It tests frozen-basis limits, finite orbit stages, escape-coordinate
lemniscates, quasiconformal wringing, Teichmuller realization, `K_0` probe
extension, strong Mittag--Leffler inverse limits, Green-gradient deformation,
and analytic continuation of component probes. These routes likewise reduce
to an exact parameter-carving map; none adds an unconditional theorem.

A fourth ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round4.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round4.md).
It tests parameter-potential level sets, finite kneading graphs, branched
coverings, hyperbolic-component unions, filled-Julia semicontinuity,
lamination quotients, shape theory, Mayer--Vietoris `K`-theory, Green-depth
induction, and first-exit paths. **No axiom was discharged.**

A fifth ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round5.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round5.md).
It tests effective quotients, Stein factorization, monotone decompositions,
pinched-disk models, polynomial-like moduli, covering-space lifting,
categorical descent, Vietoris--Begle degree-zero invariants, renormalization
coequalizers, and a formal dependency audit. **No axiom was discharged.**

A sixth ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round6.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round6.md).
It tests polynomial hulls, Riemann-map crosscuts, winding and degree
obstructions, Loewner evolution, equipotential trees, Berkovich
specialization, categorical `pi_0` base change, Runge extension, and an
explicit axiom-replacement audit. **No axiom was discharged.**

A seventh ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round7.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round7.md).
It tests universal filled-Julia incidence spaces, Hubbard trees, modulus
bounds, semialgebraic finite stages, monodromy, structural-stability strata,
external-ray incidence, `K_0` localization, universal polynomial-like
families, and a dependency audit. **No axiom was discharged.**

An eighth ten-iteration round is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_round8.md`](refs/green_sublevel_intersection_categorical_proof_attempts_round8.md).
It tests good-cover nerves, component cosheaves, persistence and Reeb graphs,
Thurston pullback contraction, extension of the near-infinity Böttcher family,
stable-component gluing, locale descent, noncommutative `K_0`, and finite
obstruction extraction. **No axiom was discharged.**

An up-to-100-attempt proof search is recorded in
[`refs/green_sublevel_intersection_categorical_proof_attempts_100.md`](refs/green_sublevel_intersection_categorical_proof_attempts_100.md).
It records one hundred markdown/Lean reductions across planar topology,
potential theory, renormalization, quasiconformal realization, finite
approximations, categorical descent, homological invariants, non-Archimedean
models, and direct axiom audits. **No axiom was discharged.**

The Efimov source inventory in
[`refs/efimov_source_inventory.md`](refs/efimov_source_inventory.md) includes
`2405.12169v3`, `2502.04123v2`, `2505.13260v2`, `2510.17010v1`, and
`2603.08653v2`. A source-level audit found no Mandelbrot, Green-function,
holomorphic-motion, or connectedness theorem in those papers; they supply
categorical/K-theoretic infrastructure, not the missing parameter carving.

## Validation

```bash
make build
make check
./scripts/verify_output.sh
```

## Core files

| Purpose | Path |
| --- | --- |
| Public root | [`Mlc.lean`](Mlc.lean) |
| Categorical root | [`Mlc/CategoricalRoot.lean`](Mlc/CategoricalRoot.lean) |
| Compatibility root | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Repaired outer-buffer input | [`Mlc/ParameterComponentApproximation.lean`](Mlc/ParameterComponentApproximation.lean) |
| Parameter frontier | [`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean) |
| Green-sublevel proof | [`Mlc/GreenSublevelConnectedDirect.lean`](Mlc/GreenSublevelConnectedDirect.lean) |
| Molecule bridge | [`Mlc/MoleculeToParameterShrink.lean`](Mlc/MoleculeToParameterShrink.lean) |
| Categorical warm-up | [`Mlc/CategoricalMandelbrot.lean`](Mlc/CategoricalMandelbrot.lean) |
| Efimov/Pacman interface | [`Mlc/EfimovCategoricalBridge.lean`](Mlc/EfimovCategoricalBridge.lean) |
| Certified finite outer stages | [`Mlc/CertifiedOrbitApproximation.lean`](Mlc/CertifiedOrbitApproximation.lean) |
| Certified inner trapping regions | [`Mlc/CertifiedTrappingRegions.lean`](Mlc/CertifiedTrappingRegions.lean) |
| Parameter classification | [`Mlc/ParameterClassification.lean`](Mlc/ParameterClassification.lean) |
| Nested parameter addresses | [`Mlc/ParameterAddressSpace.lean`](Mlc/ParameterAddressSpace.lean) |
| Finite-component bridge | [`Mlc/FiniteComponentCriterion.lean`](Mlc/FiniteComponentCriterion.lean) |
| Flow and deformation interfaces | [`Mlc/FlowInterfaces.lean`](Mlc/FlowInterfaces.lean) |
| Axiom checker | [`check_axioms.lean`](check_axioms.lean) |

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.28.0`.
