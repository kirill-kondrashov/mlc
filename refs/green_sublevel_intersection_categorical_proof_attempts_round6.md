# Sixth ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This round tests ten additional mechanisms, with special emphasis on global
planar invariants and categorical `π₀` descent. The target is

```lean
∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
  ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
    ImageConnected
      (intersection (greenSublevelApproximation c n)
        mandelbrotApproximation)
```

Writing

```text
A(c,n) = {c' | G_c(c' - c) < 2^(-n)},
```

the set-level target is

```text
A(c,n) ⊄ M  →  IsConnected (A(c,n) ∩ M).
```

Each proposed proof is stated before its first failed implication. Lean
formalization is attempted using the existing `ParaPuzzleConnectivity`,
`CategoricalMandelbrot`, and `EfimovCategoricalBridge` interfaces.

## Attempt 1/10 — polynomial hulls and full planar continua

### Proposed proof

The Mandelbrot set is a full continuum, so its polynomial hull is itself.
For `c ∈ M`, the Green sublevel `A(c,n)` is a bounded full neighborhood of
the translated filled Julia continuum. Suppose `S = A(c,n) ∩ M` is
disconnected. Polynomial convexity would give a holomorphic polynomial
separating the two components while remaining bounded on `M`. The maximum
principle on the full hull `M` would force the polynomial to be constant,
contradiction.

### First invalid step

Polynomial convexity of `M` does not imply polynomial convexity of
`A(c,n) ∩ M`. A disconnected compact subset can have a polynomial hull that
fills in a connecting bridge, so the polynomial separator need not exist.
Moreover, `A(c,n)` is open and its intersection with `M` is not automatically
polynomially convex. The maximum principle controls functions on the hull,
not the connectedness of the original subset.

### Lean formalization

The current repository has connectedness and compactness facts for `M`, but no
polynomial-hull API for the intersection. No valid theorem converts
`mandelbrot_set_connected` and source Green-sublevel connectivity into
polynomial convexity of the pullback.

### Revision

A hull argument would require a new theorem that `A(c,n) ∩ M` is polynomially
convex or has the same hull as a connected set. That theorem is at least as
strong as the target.

## Attempt 2/10 — Riemann map and equipotential crosscuts

### Proposed proof

Because `K_c` is connected, the basin of infinity is simply connected and its
Böttcher coordinate maps it to the exterior disk. The level boundary of
`A(c,n)` is therefore a smooth equipotential Jordan curve. Use a Riemann map
from `A(c,n)` to the unit disk. If `S = A(c,n) ∩ M` were disconnected, a
crosscut in the disk would separate its two components. Pull the crosscut
back to a curve in the basin and use the external potential to continue it to
infinity. Since `M` has connected complement, the curve cannot separate two
bounded pieces of `M`.

### First invalid step

A connected compact planar set can meet a Jordan domain in disconnected
pieces; connectedness of its complement does not prevent this. The
crosscut is a separator for the relative intersection, but there is no
principle forcing it to separate the whole complement of `M`. The missing
statement is exactly that the equipotential crosscut has a parameter-side
carving/landing correspondence.

### Lean formalization

The Böttcher work proves local dynamical facts and connectedness of the
un-intersected source. It does not provide a Riemann-map object whose
crosscuts map to `M`-preserving curves. The existing `ParaPuzzlePieceAt` is
not a graph-cut crosscut object.

### Revision

Use equipotential coordinates as the source of a future carving map; the
Riemann map alone does not prove the intersection connected.

## Attempt 3/10 — winding-number obstruction to a separator

### Proposed proof

Assume `S` has two components. By planar separation, choose a Jordan curve
`γ ⊂ A(c,n) \ M` whose bounded interior contains one component and excludes
the other. Since `γ` avoids `M`, every critical orbit along `γ` escapes or
has a uniformly bounded itinerary. The winding number of the critical value
around `γ` is therefore constant. At the marked parameter it is zero, while
at the other component it must be one, contradiction.

### First invalid step

Avoiding `M` does not imply that the critical orbit escapes uniformly along
the curve; the complement of `M` consists of escaping parameters, but the
escape time can vary without a uniform bound near the boundary. The claimed
winding invariant is not defined by the current Green function, which uses
the fixed map `f_c` rather than `f_{c'}`. No endpoint calculation forces
different winding numbers.

### Lean formalization

The Molecule orbit characterization can show pointwise escape outside `M`,
but it does not provide a continuous nonzero orbit function on an arbitrary
separating curve or a homotopy-invariant winding calculation. The required
parameter Green-function identity is absent.

### Revision

A degree proof needs a concrete parameter map with no zeros on the separator;
constructing that map is another form of phase--parameter realization.

## Attempt 4/10 — topological degree of the critical-value map

### Proposed proof

For a finite level, use the holomorphic critical-value polynomial

```text
p_N(c') = f_{c'}^N(0).
```

The boundary of `A(c,n) ∩ M` maps under `p_N` to the boundary of the escape
disk. If the map has degree one on the marked component, the argument
principle gives one preimage component, so the finite-stage intersection is
connected. Passing to the compact outer limit proves the target.

### First invalid step

The boundary of the frozen Green sublevel is not a level set of `p_N`, and
`M` has no proved finite-stage boundary described by `|p_N| = 2`. The degree
of `p_N` on a component can change when critical values cross the contour.
There is no theorem placing all relevant critical values outside the chosen
contour.

### Lean formalization

Orbit continuity and polynomial iteration are available, but no argument
principle/degree theorem has been connected to `outerOrbitSet N` or to the
fixed Green equipotential. The finite-stage connectedness premise remains
unproved.

### Revision

Restrict degree arguments to a polynomial-like family with a verified proper
boundary map and explicit critical-value exclusion.

## Attempt 5/10 — Loewner evolution of equipotential hulls

### Proposed proof

As the Green level increases, the equipotential domains form a Loewner-type
increasing family of simply connected hulls. Track the intersection with
`M` under the Loewner flow. A connected component could only be born or die
at a critical time when the driving function hits `∂M`. In the straddling
case, the initial component contains `c`, and the no-crossing property of
Loewner hulls prevents a second component from appearing.

### First invalid step

The Green equipotential family is a dynamical family for fixed `c`; it is not
shown to be a Loewner flow whose driving function is related to the parameter
boundary. Loewner no-crossing controls hulls in one plane, not the
intersection with an independently defined continuum `M`. A second component
can appear by a transverse crossing of `∂M` with an equipotential.

### Lean formalization

No Loewner evolution, driving function, or parameter-boundary transversality
is present. The existing harmonic/Green lemmas establish source
sublevels but no `MapsTo` statement for an evolving family of subsets of
`MandelbrotSet`.

### Revision

Loewner theory could supply regularity after a parameter conformal welding is
constructed; it cannot replace that welding.

## Attempt 6/10 — rooted tree of equipotential components

### Proposed proof

Collapse each equipotential of the dynamical basin to a vertex and each
annular band to an edge. The basin becomes a rooted tree. The connected
Green sublevel is an initial subtree. Pull the tree back through the critical
orbit itinerary map to parameter space. Since the preimage of an initial
subtree under a tree morphism is connected, the intersection with `M` is
connected.

### First missing theorem

There is no parameter tree morphism. The dynamical quotient records
`f_c`-orbits for a fixed `c`, whereas `M` records bounded critical orbits of
the varying maps `f_{c'}`. Identifying these itineraries is exactly the
parameter puzzle correspondence. A tree model without a specialization map
does not say anything about the literal parameter set.

### Lean formalization

The repository contains no quotient-to-tree construction for the basin and
no map from its tree to `MandelbrotSet`. The generic categorical tower can
express a tree morphism as input, but not derive it.

### Revision

Use tree combinatorics only after the parameter itinerary map and its
connected-fiber theorem have been formalized.

## Attempt 7/10 — Berkovich tree and specialization

### Proposed proof

Pass to the Berkovich analytification of the quadratic family over a
non-Archimedean field. The connectedness locus has a canonical tree skeleton,
and the reduction of a Green sublevel is a connected affinoid domain. The
specialization map from the Berkovich domain to the complex parameter plane
has connected fibers. The image of the connected affinoid is therefore
`A(c,n) ∩ M`.

### First missing theorem

The Berkovich specialization would be a model of the complex family, not an
already identified map onto the complex Mandelbrot set. A connected image
argument requires a continuous specialization map with exact image and
connected fibers. No comparison theorem between this non-Archimedean model
and the complex fixed-Green intersection is known in the repository.

### Lean formalization

There is no Berkovich or non-Archimedean analytic geometry dependency in the
project. Introducing such a space plus an exact specialization theorem would
be a new research-scale development and would still instantiate the same
carving interface.

### Revision

The Berkovich approach is a possible external model for the missing
realization, not an axiom-free Lean proof of the current statement.

## Attempt 8/10 — categorical `π₀` base change

### Proposed proof

In `TopCat / ℂ`, form the pullback

```text
P = greenSublevelApproximation c n ×_ℂ mandelbrotApproximation.
```

The source approximation has one connected component. If the connected
component functor `π₀` preserved this pullback along the inclusion of `M`,
then

```text
π₀(P) ≅ π₀(greenSublevelApproximation c n)
          ×_{π₀(ℂ)} π₀(M)
```

would be a singleton. Hence `P` would be connected.

### First invalid step

`π₀` does not preserve arbitrary pullbacks in `TopCat`; connectedness is not
stable under intersection of connected subspaces. Base-change preservation
requires a special fibration, open map, or homotopy-cartesian hypothesis.
The missing parameter carving theorem is precisely a condition that would
make this pullback behave like a connected quotient.

### Lean formalization

The current categorical layer defines the pullback and proves its image is
the set intersection. It has no `π₀` functor with pullback preservation, and
such a theorem would be false without extra hypotheses. The finite-etale
probe equivalence records the same obstruction in degree zero.

### Revision

State a base-change theorem only with an explicit connected-fiber/open-map
hypothesis, which reduces to `TopCatSurjectiveMorphism`.

## Attempt 9/10 — Runge approximation of a separating clopen probe

### Proposed proof

If `S = A(c,n) ∩ M` is disconnected, choose a locally constant Boolean
function on `S` separating its components. Approximate this function by a
holomorphic function on a polynomially convex neighborhood using Runge's
theorem. The approximation is nearly constant on each component and can be
continued through the connected source `A(c,n)`. The identity theorem then
forces the two constants to agree, contradiction.

### First invalid step

Runge approximation requires a suitable holomorphic function on a neighborhood
of `S`; a locally constant function on an arbitrary disconnected compact set
does not have such a holomorphic extension. Polynomial convexity of `S` is
not known and is generally false. Even a near-constant approximation does not
become exactly constant under analytic continuation.

### Lean formalization

No Runge approximation or polynomial-convex extension API is available.
The existing `FiniteEtaleKZeroProbe` theorem detects the separator but
provides no analytic extension. Adding an extension field would be an
equivalent connectedness assumption.

### Revision

Keep the probe as a precise obstruction certificate; do not infer analytic
continuation from local constancy alone.

## Attempt 10/10 — formal root audit and axiom replacement test

### Proposed proof

Replace the frontier declaration temporarily by the strongest available
conditional theorem and run the root axiom collector. If all uses of the
frontier disappear, then the conditional theorem would have discharged the
axiom. The candidate replacement is:

```lean
∀ c hc n hstraddle,
  Nonempty (DouadyHubbardYoccozCategoricalCarvingData c n)
```

### Formalization result

The conditional theorem does remove the use of the frontier *when supplied as
an additional hypothesis*, and

```lean
greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz
```

constructs the target from it. But the root still needs the universal
existence proposition. Replacing the frontier declaration by that proposition
changes its name and shape without reducing its mathematical content.

### Revision

Keep the existing frontier axiom and conditional theorem separate. The audit
confirms that connectedness transport is complete while existence of the
parameter carving remains unproved.

## Round-6 conclusion and explicit axiom status

The global polynomial, conformal, degree, tree, non-Archimedean, categorical,
and analytic-continuation routes all fail at the same point: they need an
exact parameter-side map or a theorem that is equivalent to its existence.
The current Lean development already formalizes the valid implication from
such a map to connectedness.

**AXIOM STATUS: NO AXIOM DISCHARGED.**

The checked root still uses exactly:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

No new axiom, `sorry`, or model-identification shortcut was introduced.
