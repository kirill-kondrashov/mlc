# Fifth ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This round tests ten additional proof mechanisms. The target remains

```lean
∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
  ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
    ImageConnected
      (intersection (greenSublevelApproximation c n)
        mandelbrotApproximation)
```

At set level, write

```text
A(c,n) = {c' | G_c(c' - c) < 2^(-n)}.
```

The straddling target is `A(c,n) ⊄ M → IsConnected (A(c,n) ∩ M)`.
Every proposed proof is first stated as a complete argument, then reduced to
the first missing theorem and checked against the current Lean interfaces.

## Attempt 1/10 — effective quotient and coequalizer

### Proposed proof

Let `S = A(c,n) ∩ M`. Construct an equivalence relation `R` on the connected
source `A(c,n)` by declaring two source points equivalent when they have the
same parameter straightening. Let

```text
q : A(c,n) → A(c,n)/R
```

be the quotient map. The quotient is a coequalizer in `TopCat`; identify it
with `S` by sending a class to its straightened parameter. Since continuous
images and categorical coequalizers of connected spaces are connected, `S` is
connected.

### First missing theorem

The relation `R` and its exact identification with the literal subset `S`
are not available. An arbitrary quotient of `A(c,n)` need not be the
parameter intersection; the class-to-parameter map is precisely the missing
phase--parameter realization. Moreover, proving that the quotient topology
agrees with the subspace topology on `S` is an additional exactness condition.

### Lean formalization

The existing `TopCatSurjectiveMorphism` is the quotient-free, minimal
surjective-image interface. A coequalizer construction would only replace
that structure with a relation plus an exact quotient comparison. No Lean
term can be supplied for the comparison without new geometric data.

### Revision

Use effective quotients to package a future carving construction, but do not
infer the quotient identification from connectedness of the source.

## Attempt 2/10 — Stein factorization of a proper parameter map

### Proposed proof

Construct a proper holomorphic map `p` from a connected polynomial-like
parameter space `X` onto a neighborhood of `S`. Stein factorization gives

```text
X → Spec(p_* O_X) → image(p).
```

The first map has connected fibers and the second is finite. Since `X` is
connected and the finite map is one-sheeted on the straddling component, the
image is connected. Identify the image with `S`.

### First missing theorem

Stein factorization controls a map that has already been constructed. Neither
the polynomial-like parameter space `X` nor a proper map with image exactly
`S` exists in the repository. One-sheetedness on the straddling component is
also a nontrivial parameter straightening statement.

### Lean formalization

The available proper-map results concern specified dynamical restrictions and
do not produce a proper map into `TopCat.of S`. Mathlib has no ready-made
Stein-factorization interface for the required complex-analytic family. The
conditional connected-image theorem remains valid, but the source and map
are missing.

### Revision

A future formalization can use properness as a strengthening of
`TopCatSurjectiveMorphism`; it cannot use Stein factorization as a constructor.

## Attempt 3/10 — monotone decomposition of the Mandelbrot continuum

### Proposed proof

Decompose the continuum `M` into equivalence classes consisting of points with
the same external combinatorics and the same renormalization itinerary. If
the decomposition is upper semicontinuous and every class is connected, the
quotient is a locally connected continuum. The frozen Green neighborhood
projects to a connected interval in the quotient. The inverse image of that
interval under a monotone quotient map is connected, giving `S`.

### First missing theorem

The required decomposition is not known to be upper semicontinuous without
the local-connectivity/landing information that the MLC seeks. Even for a
monotone quotient, the preimage of a connected subset is connected only when
the quotient is monotone in the precise sense that all fibers are connected
and the map is closed; these properties have not been constructed for the
Mandelbrot set or the frozen Green neighborhood.

### Lean formalization

There is no decomposition-space or monotone-quotient object in the current
formalization. The finite-etale `Bool` probe detects failure of connectedness,
but does not produce the proposed decomposition. Adding an abstract
`MonotoneQuotient` structure would merely state the missing theorem as a field.

### Revision

This route is a possible topological reformulation of the frontier, not a
proof from the current continuum facts.

## Attempt 4/10 — pinched-disk model and Moore's theorem

### Proposed proof

Start with the closed external disk and identify boundary angles whose rays
are glued by the quadratic lamination. Moore's theorem says that a
noncrossing, upper semicontinuous decomposition gives a quotient homeomorphic
to a closed disk. The image of a connected angular sector is connected.
Show that the sector corresponding to `A(c,n)` has image precisely
`A(c,n) ∩ M`.

### First missing theorem

The exact quotient map from the pinched disk to the actual Mandelbrot set is
not available without the required external-ray landing and local
connectivity theorem. The current Green sublevel is not proved to be the
image of one connected angular sector. Moore's theorem can produce a model
continuum, but not identify it with the literal `M`.

### Lean formalization

No lamination, pinched-disk quotient, or Moore decomposition is defined.
Using such a model in place of `MandelbrotSet` would change the target. The
existing categorical `ofSet` equality bridge requires literal equality of
subsets, which is exactly the unavailable identification.

### Revision

Keep the pinched-disk model conditional on a proven exact quotient and sector
preimage theorem.

## Attempt 5/10 — polynomial-like moduli and a monotone straightening map

### Proposed proof

Let `P_n` be the moduli space of polynomial-like restrictions associated to
the level-`n` Green neighborhood. The straightening map

```text
σ_n : P_n → ℂ
```

is continuous and maps the connectedness locus `C_n ⊂ P_n` onto `M`.
The parameter region `A(c,n)` is the image of a connected component of `P_n`.
If `σ_n` is monotone on that component, then

```text
σ_n(C_n ∩ component) = A(c,n) ∩ M
```

is connected.

### First missing theorem

Continuity of straightening is not enough: the preimage or image of a
connected set under a continuous map need not have the required connectedness.
The needed monotonicity and exact image equality are stronger than the
standard existence of individual straightenings. They amount to the
Douady--Hubbard parameter correspondence for the whole straddling family.

### Lean formalization

The Molecule dependency provides renormalization and polynomial-like
interfaces but no `P_n`, family-level `σ_n`, or monotonicity theorem. The
existing `PacmanRealization` structure can express the map as input, while
`TopCatSurjectiveMorphism` expresses the resulting connected image.

### Revision

Formalize family-level straightening only together with explicit continuity,
surjectivity, and exact-image fields.

## Attempt 6/10 — covering-space lifting on the complement of the postcritical set

### Proposed proof

Remove the postcritical set from the dynamical plane. The Böttcher coordinate
gives a covering of the basin, and the parameter variation defines a path of
covering maps. Lift any path in `A(c,n)` beginning at the marked parameter.
Because the source Green sublevel is simply connected after cutting along the
postcritical arcs, the lift is unique. The lifted critical orbit remains
bounded exactly when the endpoint lies in `M`; hence any two points of
`S` can be joined by a path in `S`.

### First missing theorem

The complement of the postcritical set is not a single fixed covering space
under parameter variation: the postcritical set moves with the parameter and
can collide at critical relations. The assertion that boundedness of the
lifted critical orbit is preserved along the lifted path is the desired
parameter connectedness statement, not a covering-space formal consequence.

### Lean formalization

The repository has no moving covering-space or fundamental-group API for the
quadratic basin. Existing Böttcher results are local near infinity and do not
provide a global lift over the straddling parameter set. The required path
lifting map would be a new carving construction.

### Revision

Use covering spaces only on a carefully isolated hyperbolic stratum where the
postcritical set is controlled; the general frontier remains open.

## Attempt 7/10 — effective descent for connected objects

### Proposed proof

Cover `S` by two open parameter charts arising from local Böttcher
coordinates. Their pullbacks to the connected frozen source are connected,
and their overlap is nonempty. In `TopCat`, connectedness satisfies descent
for this effective open cover: the two connected pieces glue to a connected
object. Since the descent coequalizer is the literal pullback
`A(c,n) ×_ℂ M`, the target is connected.

### First missing theorem

The required charts and their overlap are not constructed. More seriously,
the pullback of a connected source chart along the parameter map is not known
to be connected, and the descent coequalizer must be identified with the
literal set intersection. Effective descent transports connectedness after a
cover has been supplied; it does not create the cover or its maps.

### Lean formalization

`CategoricalTopologicalApproximation.lean` already models the intersection as
a pullback in `Over (TopCat.of ℂ)`. It does not provide an effective descent
cover of that pullback. The finite-etale excision structures record the same
missing restriction-surjectivity data.

### Revision

Add a concrete open-cover/carving datum if this categorical descent route is
pursued.

## Attempt 8/10 — Vietoris--Begle and degree-zero cohomology

### Proposed proof

Construct a proper surjection `q : X → S` from a connected compact space `X`
with connected fibers. Vietoris--Begle gives an isomorphism on reduced
degree-zero Čech cohomology:

```text
H~⁰(S; ℤ) ≅ H~⁰(X; ℤ) = 0.
```

Therefore `S` is connected. The connected source is the compactification of
the Green sublevel, and the fibers are straightening classes.

### First missing theorem

The cohomological implication is sound, but the map `q`, compact source, and
connected-fiber theorem are absent. Connectedness of a source alone gives the
same simpler `TopCatSurjectiveMorphism` consequence; Vietoris--Begle adds no
new way to construct the required map.

### Lean formalization

The current `FiniteEtaleKZeroProbe` is the available degree-zero shadow.
There is no Čech cohomology/Vietoris--Begle formalization in the repository.
The existing probe theorem verifies the implication conditionally, and its
missing premise is exactly restriction-surjectivity or carving.

### Revision

Use Vietoris--Begle as a future invariant-level proof after the geometric
surjection is constructed, not as a source of that surjection.

## Attempt 9/10 — renormalization coequalizer induction

### Proposed proof

For a primitive or satellite renormalizable parameter, form the finite
renormalization tower. At each level, identify parameters with the same
straightened renormalization data. The tower's transition maps are
surjective, and the final parameter intersection is the coequalizer of the
tower equivalence relation. Inductively, each level is connected; a
coequalizer of connected levels is connected. The unbounded residual branch
is handled by the strong Mittag--Leffler condition.

### First missing theorem

The tower in the repository is a dynamical/categorical interface, not a
parameter tower with a map to `A(c,n) ∩ M`. Surjectivity of transitions in
abstract `K`-theory does not imply surjectivity of parameter maps. The
residual branch also contains the separate virtual near-Molecule axiom.

### Lean formalization

`PacmanRealization`, `StrongMittagLefflerData`, and
`KTheoryLimitComparison` can state the desired induction hypotheses, but
none supplies a concrete parameter projection or coequalizer equality.
Adding that equality would be an equivalent replacement for the frontier
axiom, not a proof of it.

### Revision

Separate the renormalization residual axiom from the parameter carving
problem; neither can be discharged by an abstract tower wrapper alone.

## Attempt 10/10 — formal model-checking of the frontier implication

### Proposed proof

Use the exact Lean definition of the root and attempt to derive the target
from all imported theorems except the declaration
`green_sublevel_intersection_categorical`. If the target were a consequence
of the base interface, the axiom collector would no longer list it. Search
the imported theorem graph for a path from source connectedness, Molecule
orbit bounds, or Efimov tower data to the target. A successful path would
replace the frontier axiom by a theorem.

### Formalization result

The imported graph reaches the target only through the already recorded
conditional theorem:

```lean
DouadyHubbardYoccozCategoricalTheorem →
  GreenSublevelIntersectionCategoricalData
```

The source-connectedness theorem and all set/categorical equivalence bridges
are axiom-clean, but no theorem constructs
`DouadyHubbardYoccozCategoricalTheorem`. The axiom collector therefore
continues to report the target declaration. This is not a semantic
independence proof, but it is an exact dependency audit of the checked root.

### Revision

Retain the current frontier axiom and its minimal carving reduction. Do not
replace it with a differently named equivalent assumption merely to alter the
axiom report.

## Round-5 conclusion and explicit axiom status

The quotient, coequalizer, monotone-decomposition, pinched-disk, moduli,
covering, descent, cohomological, and renormalization routes all have the same
logical shape:

```text
construct a connected source and an exact continuous image map
  → connectedness of A(c,n) ∩ M.
```

The categorical bridge already proves this implication. The missing content
is the exact image/parameter realization, not the connectedness transport.

**AXIOM STATUS: NO AXIOM DISCHARGED.**

The checked root still uses exactly:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

No `sorry`, replacement axiom, or unverified classical identification was
introduced in this round.
