# Eighth ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This round tests gluing, persistence, and approximation mechanisms that were
not previously treated as complete proof candidates. The target is

```lean
∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
  ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
    ImageConnected
      (intersection (greenSublevelApproximation c n)
        mandelbrotApproximation)
```

At set level:

```text
A(c,n) = {c' | G_c(c' - c) < 2^(-n)},
A(c,n) ⊄ M  →  IsConnected (A(c,n) ∩ M).
```

Each attempt is first written as a complete argument, then checked against
the current Lean interfaces and revised at the first missing implication.

## Attempt 1/10 — a good-cover nerve of hyperbolic parameter charts

### Proposed proof

Cover `S = A(c,n) ∩ M` by parameter charts on which the quadratic dynamics is
structurally stable. Choose the charts small enough that every nonempty finite
intersection is connected. The nerve of this good cover is connected because
all charts attach to the chart containing `c`. The nerve theorem then gives
that `S` is homotopy equivalent to a connected simplicial complex, hence
connected.

### First missing theorem

There is no proved cover of all of `S` by structurally stable charts. Boundary
and infinitely renormalizable parameters are not covered by the hyperbolic
interior. Even if a cover existed, the nonempty finite-intersection condition
is a local form of parameter-puzzle connectivity and is not implied by the
fixed Green inequality.

### Lean formalization

The repository has no hyperbolic-chart, nerve, or nerve-theorem object. The
categorical approximation layer can represent a cover only after the chart
maps and their exact union have been supplied. The connected-image theorem
cannot construct this good cover.

### Revision

Use a nerve proof only after proving a genuine connected parameter cover,
including all boundary strata.

## Attempt 2/10 — cosheaf of connected components

### Proposed proof

For every open subset `U` of the frozen Green source, define the set of
connected components of `U ∩ M`. Restriction along inclusions gives a
cosheaf of components. The source `A(c,n)` is connected, so its component
cosheaf has one global section. If the cosheaf satisfies descent along the
Green-sublevel cover and its stalks are connected, all local components glue
to a single global component. Therefore `A(c,n) ∩ M` is connected.

### First missing theorem

A cosheaf of components can have multiple global sections even when the
ambient source is connected; the restriction maps lose information at the
boundary of `M`. Stalk connectedness does not imply global connectedness
without a specific effective-descent theorem and a cover whose overlaps
intersect inside `M`.

### Lean formalization

The current `TopCat` pullback and finite-etale probe structures do not define
a component cosheaf or its descent maps. The missing descent-surjectivity
condition is equivalent to the existing finite-etale restriction-surjectivity
criterion, so the proposed cosheaf theorem would repackage the frontier.

### Revision

Record component-cosheaf descent as a conditional interface, not as a
consequence of source connectedness.

## Attempt 3/10 — persistence of connected components across Green levels

### Proposed proof

The sets `A(c,n)` form a nested filtration. Compute the persistent
zero-dimensional homology of the filtered intersections

```text
S_n = A(c,n) ∩ M.
```

The marked component is born at the deepest level and persists toward
shallower levels. If a second component appeared at some level, its
persistence class would have to be born at a critical Green level. But the
Green function has no critical points in the basin, so no new component can
be born. Hence every `S_n` is connected.

### First invalid step

The restriction of `G_c(c' - c)` to `M` need not be a smooth function, and
its level sets on `M` can have topological changes caused by the nonsmooth
boundary of `M`, not by critical points of the dynamical Green function in
the basin. The absence of dynamical critical points does not control
criticality of the restricted parameter filtration.

### Lean formalization

No persistent homology or filtered `π₀` API exists. The proved harmonicity
of `G_c` applies off `K_c` in the dynamical plane and cannot be transferred
to `M` under translation. The needed persistence-stability theorem is absent.

### Revision

Use persistence only after defining a parameter filtration with a verified
no-new-components theorem.

## Attempt 4/10 — Reeb graph of the restricted potential

### Proposed proof

Form the Reeb graph of the function `G_c(c' - c)` restricted to `M`.
The Reeb graph of a connected compact set is connected. The sublevel
component containing `c` corresponds to a connected initial subtree. Since
`A(c,n)` is a sublevel, its inverse image in `M` is connected.

### First invalid step

The Reeb graph of a function on a connected space is connected, but the
inverse image of a connected subgraph need not be connected unless the
function is monotone on the relevant fibers. The Reeb quotient collapses
components of level sets; it does not prevent several distinct components of
a sublevel from mapping to the same graph interval.

### Lean formalization

There is no Reeb graph or quotient-fiber API for `MandelbrotSet`. The
finite-etale detector exhibits exactly the possible disconnected fibers of
the sublevel. Constructing a monotone Reeb map would be an additional
parameter-boundary theorem.

### Revision

Require connected level fibers or a monotone Reeb quotient explicitly; do not
infer sublevel connectivity from the connectedness of the Reeb graph.

## Attempt 5/10 — Thurston pullback contraction on marked dynamics

### Proposed proof

For a parameter in `S`, mark the finite orbit data selected by the Green
level. Define the Thurston pullback on the corresponding Teichmuller space.
The pullback is a strict contraction in the Teichmuller metric, so every
marked structure has a unique fixed point. Varying the mark continuously
along the connected source `A(c,n)` gives a continuous family of fixed
quadratic parameters. Its image is exactly `S`, proving connectedness.

### First missing theorem

The Thurston contraction applies to a specified postcritically finite or
controlled branched-cover model. The general straddling parameters need not
have finite postcritical sets, and the construction of a marked branched
cover from the fixed Green sublevel is missing. Exact surjectivity onto all
of `S` is the same parameter realization problem.

### Lean formalization

No Teichmuller metric, Thurston pullback, or fixed-point theorem for this
family exists in the project. The existing `PacmanRealization` interface can
record the resulting fixed-point map but cannot construct it.

### Revision

Apply Thurston theory only on a separately formalized postcritically finite
or hyperbolic stratum, with an explicit extension theorem for limits.

## Attempt 6/10 — extending the near-infinity Böttcher family to the full basin

### Proposed proof

The repository already has a jointly holomorphic Böttcher family near
infinity. For `c' ∈ A(c,n)`, choose an escape time `N` and define

```text
Φ_{c'}(z) =
  Φ_{c'}(f_{c'}^N(z))^(1 / 2^N).
```

Use the functional equation to show independence of `N`, then invert the
family on an equipotential. The inverse gives a space-holomorphic motion whose
image is exactly `A(c,n) ∩ M`. Connectedness follows from the existing
space-holomorphic carving theorem.

### First missing theorem

The near-infinity family does not automatically extend jointly across all
escape-time domains: one needs compatible branches of the `2^N`-th roots,
overlap analyticity, and a parameter domain on which the escape time is
locally constant or the branches glue continuously. At the Mandelbrot
boundary the required inverse/equipotential parameterization is precisely
the hard landing and phase--parameter theorem.

### Lean formalization

The near-infinity analytic and joint-continuity files provide the base case.
There is no basin-wide `GenuineBottcherLocalFamilyData` constructor, no
parameterized root-gluing theorem, and no exact-image proof for the
intersection. The existing `SpaceHolomorphicCarvingData` theorem can consume
this construction once completed.

### Revision

This is the most concrete route in the current codebase: extend the sound
near-infinity Böttcher family, then prove the exact carving image. It remains
unproved rather than an axiom-free shortcut.

## Attempt 7/10 — local-to-global gluing through stable components

### Proposed proof

Let `H` be the union of all local parameter neighborhoods on which the
critical orbit remains bounded for a uniform finite time. Each neighborhood
is connected and contains a point of `M`. If two such neighborhoods overlap,
their bounded-orbit certificates agree by uniqueness of the critical
trajectory. The overlap graph is therefore connected, and the union is
connected. Compactness and the outer orbit identity give

```text
closure(H) = A(c,n) ∩ M.
```

Connectedness passes to the closure.

### First missing theorem

Uniform finite-time boundedness is not an open condition for the infinite
bounded-orbit set at boundary parameters. The overlap graph may omit
infinitely renormalizable points, and the closure equality is exactly a
density/parameter-approximation theorem. A connected dense subset of a set
does not imply that the chosen finite-stage union has the required closure
without proving density.

### Lean formalization

The inner and outer orbit approximations provide finite constraints but no
connected local `M`-neighborhoods or overlap graph. The generic closure
connectedness theorem is available only after the connected dense subset is
constructed.

### Revision

Use this route as a finite-stage specification: prove local connectedness and
density separately before invoking the closure theorem.

## Attempt 8/10 — locale/frame formulation of connectedness

### Proposed proof

Replace the subspace topology on `S` by its frame of opens. A space is
connected exactly when its frame has no nontrivial complemented element.
The frame of the Green source has only trivial complemented elements.
Effective descent for the inclusion `S ↪ A(c,n)` transfers complemented
elements from `S` to the source, so `S` is connected.

### First missing theorem

Open-set descent along an arbitrary closed or non-open subspace is not
effective in the required direction. A clopen separation of `S` need not
extend to a complemented element of the frame of `A(c,n)`. The extension
property is exactly the missing restriction-surjectivity of locally constant
probes.

### Lean formalization

The project uses ordinary `TopCat` subspaces and `LocallyConstant S Bool`;
no locale/frame library is instantiated for the target. The finite-etale
equivalence already proves the same obstruction in concrete Boolean form.

### Revision

Locales provide a clean reformulation of the obstruction but no new
axiom-free extension theorem.

## Attempt 9/10 — noncommutative `K₀` of a pullback algebra

### Proposed proof

Assign a commutative algebra of continuous functions to each approximation.
The pullback intersection corresponds to a tensor product or homotopy
pullback of algebras. If the source and `M` algebras have no nontrivial
idempotents and the tensor-product map is faithfully flat, then the
intersection algebra has no nontrivial idempotents. Therefore the
intersection is connected. Efimov's localizing-invariant formalism supplies
the required `K₀` descent.

### First missing theorem

Faithful flatness and homotopy-pullback identification are not automatic for
algebras of continuous functions on arbitrary planar subspaces. The
intersection algebra can acquire idempotents even when both factor algebras
do not. Efimov's abstract categorical invariants do not identify the
specific analytic function algebras or prove faithful flatness.

### Lean formalization

The repository has only the finite-etale `K₀` shadow, not C*-algebras,
derived tensor products, or faithful-flat descent. Introducing those objects
would still require an exact geometric excision theorem.

### Revision

Retain `K₀` as a diagnostic language and isolate faithful-flat descent as a
separate, explicit future hypothesis.

## Attempt 10/10 — finite obstruction extraction and exact dependency audit

### Proposed proof

Assume `S` is disconnected. Compactness gives a clopen Boolean probe
separating two components. Try to push this probe backward through every
available representation: outer orbit stages, inner orbit stages, pullback
approximations, and the Efimov/Pacman tower. If it descends to a finite stage,
connectedness of that stage contradicts it. If it does not descend, strong
Mittag--Leffler stabilization should force it to descend eventually.

### First invalid step

The existing outer stages are compact but not known to be connected, and the
inner stages do not have the required connectedness or probe-surjectivity
properties. Strong Mittag--Leffler data concern abstract ranges in a tower;
they do not imply geometric descent of a locally constant function on the
literal parameter intersection.

### Lean formalization

The finite-etale descent structures make the missing assumption explicit:
stage connectedness and restriction-surjectivity are fields, not consequences
of `StrongMittagLefflerData`. The axiom collector still reaches the target
only through the explicit frontier declaration or the conditional carving
theorem.

### Revision

Use finite obstruction extraction to state a minimal future theorem:
connected finite geometric stages plus probe-surjective bonding maps imply the
frontier. Do not infer those fields from abstract tower stabilization.

## Round-8 conclusion and explicit axiom status

The new gluing, persistence, Reeb, Thurston, basin-extension, locale, and
`K₀` routes all reduce to one of three missing inputs:

1. connected finite parameter stages;
2. effective descent of component probes;
3. an exact space-holomorphic or continuous carving map.

The existing Lean development proves the transport from (3) to the target and
the equivalence between (2) and connectedness, but does not prove any of the
three missing inputs from the current base axioms.

**AXIOM STATUS: NO AXIOM DISCHARGED.**

The checked root still uses exactly:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

No new axiom, `sorry`, or unproved identification of the full Green model
with a classical graph-cut parapuzzle was introduced.
