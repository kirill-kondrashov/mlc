# Second ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This is a second, independent ten-step attempt to discharge the remaining
frontier. The target remains

```lean
∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
  ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
    ImageConnected
      (intersection (greenSublevelApproximation c n)
        mandelbrotApproximation)
```

The set-level form is

```text
A(c,n) ⊄ M  →  IsConnected (A(c,n) ∩ M),
A(c,n) = {c' | G_c(c' - c) < 2^(-n)}.
```

Each iteration below starts with a complete proposed argument, identifies the
first invalid implication, and records the corresponding Lean status.

## Attempt 1/10 — continuum complement and simply connected sublevels

### Proposed proof

For `c ∈ M`, the filled Julia set `K_c` is a continuum and the Green function
is zero exactly on `K_c`. The sublevel `A(c,n)` is a bounded connected open
neighborhood of `c + K_c`. Suppose `A(c,n) ∩ M` has two components. By planar
separation, a complementary continuum in `A(c,n) \ M` separates those
components. Since all components of the complement of a full continuum are
unbounded, such a separator must meet the equipotential boundary. The
straddling hypothesis would then force the separator to cross the connected
filled-Julia core, a contradiction.

### Formalization result

The first separation claim is false without additional hypotheses: a connected
open neighborhood of a continuum can meet another continuum in several
components, and complement components need not supply the asserted separator
inside the neighborhood. Fullness of the Mandelbrot set and the required
local-connectivity properties are not available axiom-free. The existing
Green-sublevel proof establishes only connectedness of `A(c,n)`, not the
planar separation assertion.

### Revision

Replace the informal separator with an explicit phase--parameter arc or
surjective carving map. This is not a consequence of continuum theory alone.

## Attempt 2/10 — proper maps and connected components

### Proposed proof

Use a proper polynomial-like map from a dynamical puzzle domain to a target
domain. The Molecule dependency proves that proper restrictions preserve
compactness and that a proper pullback restricted to a target connected
component remains proper. Apply this to the Green sublevel and then transport
the resulting connected component to parameter space.

### Formalization result

The available proper-map lemmas act on a specified map
`f : X → Y`, its source/target domains, and a connected component already
chosen in `Y`. They do not construct a map from a dynamical puzzle domain to
the parameter set `A(c,n) ∩ M`. In particular, `Molecule.RenormalizationPullback`
produces dynamical renormalization domains, not a parameter realization.

The formalized proper-map API therefore proves only:

```text
given a parameter realization map with proper restriction,
the corresponding component transport is valid.
```

It does not produce the realization map or its exact image.

### Revision

Add properness only as a field of the missing carving datum; do not treat it as
the datum itself.

## Attempt 3/10 — straightening map from polynomial-like families

### Proposed proof

For each finite puzzle level, construct a polynomial-like restriction
`g_{c'}`. The Douady--Hubbard straightening theorem sends `g_{c'}` to a
quadratic parameter `s(c')`. The locus of connected filled Julia sets is the
preimage of `M` under `s`. If the straightening map is continuous and proper
on the connected source, its preimage is connected and equals
`A(c,n) ∩ M`.

### Formalization result

Three separate fields are missing:

1. a polynomial-like family indexed by every `c' ∈ A(c,n)`;
2. continuity/properness of the straightening map in that parameter;
3. equality between its connectedness locus and the literal set `M`.

The current Molecule structures encode individual polynomial-like models and
renormalization relations, but no family-level straightening map into
`TopCat.of ℂ`. Thus the proposed equality is exactly another form of the
parameter realization theorem.

### Revision

State a family-level straightening/carving structure explicitly. Its exact
image field is still the frontier.

## Attempt 4/10 — external-ray pairs and finite graph cuts

### Proposed proof

Choose the finitely many external rays landing at the level-`n` puzzle
vertices. Their union with the equipotential forms a finite planar graph.
The component containing the marked point is a topological disk. Holomorphic
motion transports this graph to parameter space. The parameter component
intersected with `M` is connected because it is the image of the connected
dynamical component.

### Formalization result

This is the classical route, but the current source is not this graph-cut
piece. The repository's `DynamicalPuzzlePiece` is the component of a full
Green sublevel; no ray landing data, finite graph, holomorphic motion, or
parameter graph is defined. The proved identity

```lean
iInter_green_sublevel_translate_eq_translate_filledJulia
```

also shows that the current full-sublevel tower does not have the graph-cut
shrinking behavior needed here.

### Revision

Either replace the target with a new graph-cut parapuzzle target, or keep the
literal target and provide an exact full-sublevel carving map. No classical
ray theorem can be silently substituted.

## Attempt 5/10 — harmonic measure and maximum principle

### Proposed proof

On every component of `A(c,n) \ K_c`, the Green function is harmonic. If
`A(c,n) ∩ M` had two components, take a harmonic measure separating them.
The maximum principle would force this harmonic measure to be constant on the
filled-Julia boundary, contradicting the existence of two parameter
components.

### Formalization result

The available harmonic API proves harmonicity of `G_c` in the basin and uses
the minimum principle to show that every component of the full sublevel meets
`K_c`. It does not provide harmonic measure for the parameter set `M`, nor a
boundary regularity theorem identifying its values on `∂M`. The maximum
principle controls the dynamical source, not the parameter intersection.

### Revision

The required boundary-value theorem is a parameter-plane realization theorem
and must be added explicitly if this route is pursued.

## Attempt 6/10 — renormalization pullback inverse limit

### Proposed proof

Represent a straddling parameter piece as an inverse limit of connected
renormalization pullbacks. Every finite pullback is connected by the proper
degree-two theorem. The inverse limit of compact connected stages is
connected, and its image under the parameter projection is
`A(c,n) ∩ M`.

### Formalization result

The inverse-limit connectedness theorem is available for a specified nested
family of compact connected sets. The missing identification is the
parameter projection:

```text
inverse-limit renormalization data → A(c,n) ∩ M.
```

The existing `RenormalizationTower` contains renormalization objects and
relations, but no map into the parameter plane and no theorem that its image is
the Green-sublevel/Mandelbrot pullback. The limit argument therefore stops at
an abstract dynamical continuum.

### Revision

Add a conservative parameter realization to the tower. This is the same
missing bridge as the categorical carving theorem.

## Attempt 7/10 — boundary-local-connectivity and prime ends

### Proposed proof

The Green sublevel boundary is an equipotential. Use prime-end theory to
identify its accessible arcs, then show that every component of
`A(c,n) ∩ M` is attached to the marked component through an accessible
boundary arc. The union is connected.

### Formalization result

Prime-end accessibility of the relevant Mandelbrot boundary is not available.
More importantly, asserting enough boundary landing and continuous extension
to make the attachment argument work is already a local-connectivity-type
statement. The target is not discharged by the existence of prime ends for
the basin alone.

### Revision

Treat boundary extension and landing as explicit hypotheses of a carving
theorem, not as consequences of the current topology.

## Attempt 8/10 — Alexander duality and separation

### Proposed proof

If `A(c,n) ∩ M` is disconnected, Alexander duality yields a nontrivial
cohomology class in its complement. Use the Green function and the connected
basin to show that the complement has no such class. Therefore the
intersection is connected.

### Formalization result

Alexander duality relates reduced homology of a compact subset to cohomology
of its complement, but the present target is an open-sublevel intersection
and no compactification/relative pair has been constructed. Even after
compactification, the Green basin does not determine the complement of
`A(c,n) ∩ M`: the missing parameter-boundary geometry remains. No available
homology computation proves the needed vanishing.

### Revision

Use duality only as a diagnostic for the missing separator; it cannot replace
the phase--parameter theorem.

## Attempt 9/10 — finite-stage regular epimorphisms

### Proposed proof

For each outer stage `O_N`, construct a connected source `D_N(c,n)` and a
surjective continuous map

```text
D_N(c,n) → A(c,n) ∩ O_N.
```

Make the maps compatible under `N`, pass to the compact inverse limit, and
use the target equality `⋂ N O_N = M` to obtain a surjection onto
`A(c,n) ∩ M`.

### Formalization result

The generic inverse-limit and connected-image steps can be expressed using
the existing `TwoSidedSetApproximation` and
`TopCatSurjectiveMorphism` interfaces. The new data required at each finite
stage are precisely the parameter-carving maps. Neither the finite maps nor
their compatibility follows from the orbit constraints. Thus this route
repackages, but does not prove, the missing theorem.

### Revision

Keep the finite-stage formulation as a useful future interface, but require
the exact image and compatibility fields explicitly.

## Attempt 10/10 — axiom-minimality and exact equivalence

### Proposed proof

Minimize the missing assumption. The source `A(c,n)` is connected. Therefore
the smallest sufficient input is a continuous surjection from `A(c,n)` onto
`A(c,n) ∩ M`; holomorphicity, properness, `K`-theory, and renormalization are
stronger implementation choices. Formalize this minimal input, prove the
connected-image theorem, and compare its quantification with the current
categorical frontier.

### Formalization result

The repository already formalizes this minimal implication through
`TopCatSurjectiveMorphism` and
`isConnected_of_topCatSurjectiveMorphism`. The stronger constructors
`SpaceHolomorphicCarvingData.toDouadyHubbardYoccozCategoricalCarvingData` and
`greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz` provide the
Lean proof. The missing field is existence of the surjection for every
straddling `(c,n)`.

This is not a disguised proof: a surjection from a connected source is
strictly additional geometric data, and its existence is not derivable from
the current orbit, Green, Molecule, or Efimov interfaces.

## Round-2 conclusion and axiom surface

The second ten attempts produce no unconditional discharge. The exact
formalized consequence is:

```lean
DouadyHubbardYoccozCategoricalTheorem →
  GreenSublevelIntersectionCategoricalData
```

The checked root still has exactly two project-level axioms:

```text
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

alongside Lean foundations `Quot.sound`, `propext`, and `Classical.choice`.
The round-2 work does not add, remove, or rename any axiom. The remaining
obligation is the existence of a genuine parameter-carving realization,
possibly supplied through a compatible finite-stage outer/inner system.
