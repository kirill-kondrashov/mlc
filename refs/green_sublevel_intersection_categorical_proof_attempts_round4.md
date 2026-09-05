# Fourth ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This round starts from the exact current frontier and tests ten mechanisms not
used in the first three reports. The target is

```lean
∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
  ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
    ImageConnected
      (intersection (greenSublevelApproximation c n)
        mandelbrotApproximation)
```

At set level:

```text
A(c,n) ⊄ M  →  IsConnected (A(c,n) ∩ M),
A(c,n) = {c' | G_c(c' - c) < 2^(-n)}.
```

Each section gives a complete proposed argument, then identifies the first
unproved implication and its Lean status. A conditional theorem is not counted
as a discharge.

## Attempt 1/10 — a parameter Green potential and subharmonic level sets

### Proposed proof

Define the parameter Green function

```text
G_M(c') = G_{c'}(c').
```

The Mandelbrot set is its zero set, and `G_M` is continuous and
subharmonic on the parameter plane. For a fixed `c ∈ M`, consider

```text
H_λ(c') = G_M(c') + λ G_c(c' - c)
```

with `λ > 0`. The first term penalizes leaving `M`, while the second term
controls the frozen Green neighborhood. If `A(c,n) ∩ M` had two components,
the minimum of `H_λ` on the compact closure of the straddling piece would be
attained in both components. Letting `λ → 0` and applying the strong minimum
principle to `H_λ` would force a connecting zero arc, proving connectedness.

### First invalid step

Subharmonicity controls maxima, not the connectedness of zero sets or
sublevel intersections. Even smooth subharmonic functions can have
disconnected zero sets and disconnected intersections of two sublevel sets.
The proposed minimum-principle conclusion does not follow. Moreover, the
parameter identity `G_M(c') = G_{c'}(c')` and its required regularity are not
present in the repository.

### Lean formalization

The existing harmonic API handles `G_c` in the dynamical variable. There is no
parameter Green function, no theorem that its zero set is exactly `M` in the
required form, and no subharmonic zero-set connectedness theorem. Lean can
formalize the conditional implication “a suitable deformation of `H_λ`
connects the zero set,” but cannot construct that deformation.

### Revision

Treat a parameter Green function as a possible bridge to a future proof, not
as a connectedness theorem by itself.

## Attempt 2/10 — finite kneading and combinatorial itinerary graphs

### Proposed proof

For a fixed level `n`, record the finite itinerary of the critical orbit of
`f_{c'}` relative to the equipotential partition determined by `c`. The
admissible itineraries form a finite directed graph. Each edge corresponds to
a connected parameter cylinder, and adjacent cylinders meet along a common
critical orbit boundary. The straddling intersection `A(c,n) ∩ M` is the
union of all admissible cylinders in the connected component of the marked
itinerary. A finite union of connected sets with a connected intersection
graph is connected.

### First missing theorem

The current frozen Green sublevels do not define a finite Markov partition in
parameter space. To make the argument work one must prove:

1. every itinerary cylinder is connected;
2. its boundary is represented by the required equipotential/ray graph;
3. every adjacent graph edge gives a nonempty intersection;
4. admissibility is equivalent to membership in `M`.

These are precisely graph-cut parapuzzle and parameter--dynamical
correspondence statements.

### Lean formalization

No finite itinerary or Markov partition type maps to `Set ℂ` in the current
source. The existing `ParaPuzzlePieceAt` is explicitly a full Green sublevel,
not a graph-cut cell. The finite union connectedness lemma is standard, but
none of its required geometric premises can be instantiated.

### Revision

Introduce genuine graph-cut parapuzzles as a separate model before attempting
this route; do not identify them with the current target.

## Attempt 3/10 — branched covering and Riemann--Hurwitz

### Proposed proof

For each finite time `N`, define the critical-value map

```text
p_N(c') = f_{c'}^N(0).
```

The finite escape condition is a preimage of a disk under `p_N`. Analyze
`p_N` as a branched covering. Riemann--Hurwitz shows that the component
containing the marked parameter has no additional branch component inside the
straddling Green sublevel. Therefore the finite-time set is connected.
Pass to the decreasing compact intersection to obtain `A(c,n) ∩ M`.

### First invalid step

Riemann--Hurwitz computes Euler characteristics of a specified covering; it
does not show that the inverse image of a disk is connected. One must control
all critical values of `p_N` relative to the disk and prove that the relevant
component contains every admissible parameter. Neither follows from the
straddling hypothesis.

### Lean formalization

The orbit-polynomial maps can be defined and their continuity is available
through `Molecule.continuous_orbit`. There is no parameter branched-covering
API giving connected fibers or a Riemann--Hurwitz component theorem. The
required finite-stage premise is exactly the one missing from the outer
approximation route.

### Revision

Use Riemann--Hurwitz only after a concrete polynomial-like parameter family
and a chosen proper component have been constructed.

## Attempt 4/10 — density of hyperbolic components and connected union

### Proposed proof

Approximate `M` inside `A(c,n)` by the union of hyperbolic components whose
closures meet the marked stratum. Every hyperbolic component is connected,
and the closures of components with adjacent internal addresses meet at
parabolic or Misiurewicz parameters. The adjacency graph is connected because
the internal-address tree is connected. The closure of this union is
`A(c,n) ∩ M`, hence the target is connected.

### First missing theorem

The equality between this hyperbolic-component closure and the full
intersection requires a density theorem for hyperbolicity in the relevant
parameter region. That density statement is open in the required generality
and is stronger than what is available from the Molecule dependency. Even
assuming density, the claimed adjacency and landing data are not available
for arbitrary complex parameters.

### Lean formalization

The repository contains `MandelbrotSet` and its connectedness but no
hyperbolic-component decomposition, internal-address tree, or density theorem.
Adding a union of known connected subsets would prove only a subset of the
target unless the exact closure equality is supplied.

### Revision

This route is useful for hyperbolic strata, but cannot prove the general
straddling statement without a new density/landing theorem.

## Attempt 5/10 — upper semicontinuity of filled Julia sets

### Proposed proof

For `c' ∈ M`, the filled Julia set `K_{c'}` is connected. Use upper
semicontinuity of `c' ↦ K_{c'}` on `M` and the fact that the fixed source
`c + K_c` lies inside `A(c,n)`. If `A(c,n) ∩ M` were disconnected, upper
semicontinuity would split the family of critical orbit compacta into two
disjoint open classes. Connectedness of the parameter family would prevent
such a split.

### First invalid step

Upper semicontinuity of a set-valued map does not imply connectedness of the
parameter set on which its values meet a fixed open set. A continuous family
of connected compacta can enter and leave an open region in disconnected
parameter subsets. The argument needs a lower-semicontinuity or a monotone
intersection property that is not true in general.

### Lean formalization

No hyperspace topology for `c' ↦ K_{c'}` is present. More importantly, even a
future hyperspace formalization would provide only continuity properties, not
the claimed connectedness of the parameter inverse image. The existing
filled-Julia connectedness theorem is pointwise in `c'`.

### Revision

Use set-valued continuity only as auxiliary control for a separately supplied
parameter carving map.

## Attempt 6/10 — lamination quotient and connected preimages

### Proposed proof

Model the boundary of `M` by the quotient of the external-angle circle under
the quadratic minor lamination. A Green sublevel `A(c,n)` corresponds to an
interval or finite union of angle sectors. Its intersection with the quotient
is the quotient of a connected angle set, so it is connected. The quotient map
then gives the desired parameter intersection.

### First missing theorem

The lamination quotient description of the actual Mandelbrot set with the
required continuous surjection is available only under a local-connectivity
/landing theorem. Without MLC, the external-angle quotient is a model or
combinatorial shadow, not a proven topological presentation of `M`.
Furthermore, the current `A(c,n)` is defined by a fixed dynamical Green
function and has no proved angle-sector preimage.

### Lean formalization

No external-angle quotient, minor lamination, or quotient map onto
`MandelbrotSet` is defined. The categorical approximation layer cannot infer
such a quotient. Replacing `M` by a lamination model would change the theorem
rather than prove the current one.

### Revision

A lamination route must first prove a continuous exact model map and an
identification of the frozen Green sublevel with its angle preimage.

## Attempt 7/10 — shape theory and cell-like neighborhoods

### Proposed proof

The connected compact set `M` is a continuum. The sets `A(c,n)` are
neighborhoods of the continuum `c + K_c` with boundaries given by smooth
equipotentials. If these neighborhoods are cell-like and the inclusion
`A(c,n) ∩ M ↪ M` is shape-equivalent to a connected neighborhood, then shape
theory implies vanishing reduced `H_0`. For compact locally connected subsets
of the plane, vanishing reduced `H_0` is equivalent to connectedness.

### First invalid step

Cell-likeness of `A(c,n) ∩ M` is exactly the desired assertion in disguise:
shape equivalence does not follow merely from `A(c,n)` being a smooth
neighborhood. A disconnected compact set can have the same ambient
cohomological data in degrees above zero as a connected one; `H_0` must be
computed directly. The required local connectedness is also the MLC issue.

### Lean formalization

Mathlib does not provide the needed planar shape-theory or cell-like
decomposition API. The existing finite-etale `K₀` detector proves that a
nonconstant `Bool` probe detects disconnectedness, but no shape argument makes
that probe vanish.

### Revision

Use shape/cohomology as an obstruction detector. A successful shape proof
still needs a geometric exact-image or extension theorem.

## Attempt 8/10 — Mayer--Vietoris and categorical `K`-theory

### Proposed proof

Let `S = A(c,n) ∩ M`. Cover `A(c,n) ∪ M` by the two open thickenings of
`A(c,n)` and `M`. Since both factors are connected, the Mayer--Vietoris
sequence in reduced degree zero gives

```text
H₁(A ∪ M) → H₀(S) → H₀(A) ⊕ H₀(M) → H₀(A ∪ M).
```

If `A ∪ M` has trivial reduced `H₁`, then the map into `H₀(S)` vanishes and
`H₀(S)` is trivial. The finite-etale `K₀` formulation then yields
connectedness.

### First missing theorem

The relevant Mayer--Vietoris map has an `H₁(A ∪ M)` term; connectedness of the
union does not make that term vanish. The union may contain loops created by
the way `A` and `M` overlap. No proof that `A(c,n) ∪ M` is simply connected or
has trivial first homology is available.

### Lean formalization

The repository formalizes the degree-zero probe shadow but not singular,
Čech, or stable `K`-theory Mayer--Vietoris. Even with an external
Mayer--Vietoris theorem, the required `H₁` vanishing would be a new geometric
input. Efimov's abstract localizing-invariant interfaces do not instantiate
this parameter pair.

### Revision

Record a future sufficient condition:
`H₁(A(c,n) ∪ M) = 0` plus a suitable excision theorem. It is conditional and
strictly stronger than the current base axioms.

## Attempt 9/10 — induction on the Green depth

### Proposed proof

Use the functional equation

```text
G_c(f_c(z)) = 2 G_c(z).
```

The map `z ↦ f_c(z)` sends the depth `n+1` dynamical sublevel into the
depth `n` sublevel. Translate back to parameters by

```text
T_c(z) = c + f_c(z).
```

Assume the depth-`n` intersection is connected. Pull it back through `T_c`
and use the degree-two branched-covering structure to prove that the
depth-`n-1` intersection is connected. Induction starts in the subset stratum.

### First invalid step

The translated map `T_c` is dynamical, not a parameter map preserving `M`.
There is no implication

```text
c' ∈ M  →  T_c(c' - c) ∈ M
```

or its inverse. Therefore the functional equation controls only the source
Green sublevels; it does not transport the parameter intersection.

### Lean formalization

The functional equation and dynamical sublevel inclusions are available.
The missing `MapsTo` statement into `MandelbrotSet` cannot be proved from the
current orbit characterization. Any added hypothesis of this form would be a
parameter-carving axiom.

### Revision

Use depth induction only after constructing a parameter-compatible
renormalization/straightening map.

## Attempt 10/10 — first-exit path argument and minimal separator

### Proposed proof

The open connected set `A(c,n)` is path-connected. Choose points in two
components of `A(c,n) ∩ M` and a path in `A(c,n)` between them. The path has a
first exit from `M` and a last re-entry. The segment between these events lies
in `A(c,n) \ M` and has endpoints on `∂M`. Follow the external basin
coordinate along this segment. Since the path remains inside one Green
sublevel, the corresponding dynamical path remains in the connected
sublevel of `G_c`; it must connect the two endpoint parameters through `M`,
contradicting the separation.

### First invalid step

There is no parameter-to-dynamical map sending an arbitrary path in
`A(c,n)` to a path in the basin of `f_c` while preserving membership in `M`.
The translation `c' ↦ c' - c` only identifies the un-intersected source with
a dynamical Green sublevel. It does not identify `M` with a dynamical
connectedness condition for `f_c`.

### Lean formalization

Lean can provide the source connectivity and, with additional path-space
lemmas, a path in `A(c,n)`. It cannot prove the required endpoint
continuation in `M`; the missing `MapsTo`/exact-image statement is precisely
`TopCatSurjectiveMorphism` or an equivalent carving datum.

### Revision

The first-exit argument is a useful diagnostic for what the carving map must
preserve, but it is not an axiom-free proof.

## Round-4 conclusion and explicit axiom status

The new attempts do not discharge the frontier. The genuinely reusable
formal reductions are:

```text
finite outer stages + connected finite-stage intersections
  → connected target;

Mayer--Vietoris + H₁(A(c,n) ∪ M)=0
  → trivial degree-zero component probe;

exact parameter carving
  → connected Green-sublevel/Mandelbrot intersection.
```

The first two require new geometric hypotheses. The third is already
formalized through `TopCatSurjectiveMorphism`.

**AXIOM STATUS: NO AXIOM DISCHARGED.**

The root still uses exactly:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

No new axiom, `sorry`, or replacement formulation was introduced in this
round. The target frontier remains the existence of an exact parameter
carving/realization map for every straddling full Green sublevel.
