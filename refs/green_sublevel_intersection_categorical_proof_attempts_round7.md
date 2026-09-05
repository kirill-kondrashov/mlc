# Seventh ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This round tests ten new mechanisms centered on universal incidence spaces,
Hubbard-tree combinatorics, quantitative annulus control, finite
semialgebraic approximations, and categorical `K₀` descent. The target is

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
the existing Lean definitions and reduced to its first missing theorem.

## Attempt 1/10 — the universal filled-Julia incidence space

### Proposed proof

Define

```text
I(c,n) = {(c',z) | c' ∈ A(c,n), z ∈ K_{c'}}.
```

The projection `π : I(c,n) → ℂ` has image exactly `A(c,n) ∩ M`: a parameter
belongs to `M` precisely when its filled Julia set is nonempty and bounded.
If `I(c,n)` is connected, its continuous projection is connected, proving the
target. To prove `I(c,n)` connected, use that every fiber `K_{c'}` is a
continuum and that the family is upper semicontinuous over the connected
source `A(c,n)`.

### First missing theorem

Connected fibers and upper semicontinuity do not imply connectedness of the
total space when the base is not already known to be connected after
restriction to the relevant parameter locus. The incidence space contains
fibers over escaping parameters as well, and its projection image is not
automatically `A(c,n) ∩ M` without a precise bounded-orbit/fiber definition.
The needed lower-continuity and parameter realization are absent.

### Lean formalization

The repository has pointwise filled-Julia connectedness, but no hyperspace
topology or universal incidence object for `c' ↦ K_{c'}`. A projection theorem
would be a valid conditional connected-image result, not a construction of a
connected incidence space.

### Revision

Use `I(c,n)` as a future source for a carving map only after proving its
connectedness and the exact projection image.

## Attempt 2/10 — Hubbard trees and regulated arcs

### Proposed proof

For postcritically finite parameters, the Hubbard tree is a finite connected
tree containing the critical orbit. Regulated arcs in the tree determine the
parameter puzzle boundaries. If two parameters in `A(c,n) ∩ M` lie in
different components, their Hubbard trees would require a separating regulated
arc. Pull the arc back under the quadratic map; the tree property forces it
to pass through the critical orbit, contradicting the common level-`n`
Green bound. Approximate general parameters by postcritically finite ones and
pass to the limit.

### First missing theorem

The postcritically finite argument does not automatically extend to arbitrary
parameters. One needs density in the relevant parameter intersection,
uniform control of Hubbard-tree arcs, and identification of their limits with
the literal frozen Green sublevel. These are parameter puzzle/landing
theorems, not consequences of pointwise Hubbard-tree connectivity.

### Lean formalization

No Hubbard-tree, regulated-arc, or postcritically finite density API is in
the project. The Yoccoz dependency is used only through existing stated
interfaces and does not provide the required exact map into
`A(c,n) ∩ MandelbrotSet`.

### Revision

Restrict this route to a separately formalized postcritically finite stratum;
do not infer the full frontier by an unproved limiting theorem.

## Attempt 3/10 — modulus bounds for a separating annulus

### Proposed proof

If `S = A(c,n) ∩ M` is disconnected, planar separation produces a doubly
connected region `U` in `A(c,n) \ M` separating two components. Its modulus is
positive. The equipotential boundary of `A(c,n)` gives an upper modulus bound,
while a priori bounds for the quadratic family give a lower bound tending to
infinity as the Green depth increases. For sufficiently deep levels these
bounds contradict. The finitely many shallow levels lie in the subset
stratum.

### First missing theorem

The existence of an annulus with the required quantitative modulus and the
claimed lower bound are not supplied by the current Green geometry. The
residual near-Molecule a priori bounds concern renormalization scales, not
arbitrary components of the complement of a fixed parameter intersection.
There is no theorem forcing every separator to have a modulus in the
controlled regime.

### Lean formalization

The repository has no extremal-length or annulus-modulus API connected to
`MandelbrotSet`. The `residualOpenVirtualNearMoleculeAxiom` is intentionally
separate and cannot be silently used to provide a parameter-separator bound.

### Revision

A modulus proof would need a new quantitative parameter-puzzle theorem
excluding separating annuli; this is a genuine additional input.

## Attempt 4/10 — finite-stage semialgebraic cell decomposition

### Proposed proof

For each `N`, the outer orbit stage

```text
O_N = {c' | ‖c'‖ ≤ 2 ∧ ∀ k ≤ N, ‖f_{c'}^k(0)‖ ≤ 2}
```

is defined by finitely many polynomial inequalities in the real and
imaginary parts of `c'`. It is therefore semialgebraic. Cylindrical
algebraic decomposition partitions `A(c,n) ∩ O_N` into finitely many cells.
The cell containing the marked parameter meets every admissible cell through
the orbit-boundary adjacency graph, so the finite stage is connected. The
nested compact intersection then proves the target.

### First missing theorem

Semialgebraicity gives finite cell decompositions, not connectedness. The
adjacency graph may have several components, and the Green inequality is not
part of the finite polynomial constraints in a way that proves all cells
attach. A uniform connectivity theorem for all `N` is exactly the missing
finite-stage result.

### Lean formalization

No real-algebraic cell decomposition API is imported. More importantly,
adding such an API would not prove the required adjacency statement. The
existing outer-limit theorem can consume connected finite stages but cannot
derive them from finite polynomial inequalities.

### Revision

Use semialgebraic decomposition for explicit low iterates or computational
experiments only; it is not an abstract proof of the all-level frontier.

## Attempt 5/10 — monodromy of critical-orbit analytic branches

### Proposed proof

On the complement of the postcritical discriminant, the iterated critical
value functions are holomorphic. Pick a path in the connected frozen Green
sublevel and analytically continue the critical-orbit branch. Monodromy around
a discriminant point permutes branches, but the bounded branch containing
`c` is invariant because the critical point is marked. Therefore the set of
parameters with bounded critical orbit is path-connected inside `A(c,n)`.

### First missing theorem

The critical orbit is not a multivalued analytic branch whose boundedness is
preserved by monodromy. It is a single polynomial function of the parameter
at each finite time, while the infinite boundedness condition is a limit
condition. Crossing the escaping boundary can change boundedness without
creating a branch permutation. Monodromy therefore does not preserve `M`.

### Lean formalization

Finite iterate continuity is available, but no analytic continuation object
for the infinite critical orbit or monodromy action is defined. The required
uniform-in-time boundedness along paths is stronger than every finite
iterate theorem in the repository.

### Revision

Monodromy may organize hyperbolic/finite-stage strata, but it cannot replace
the infinite parameter connectedness theorem.

## Attempt 6/10 — structural stability strata and boundary closure

### Proposed proof

The interior of `M` is a union of hyperbolic components, each path-connected.
Within a component, structural stability gives a holomorphic motion of the
Julia set and preserves the Green inequality. The union of all components
meeting `A(c,n)` has a connected incidence graph because components meet at
parabolic boundaries. Its closure is `A(c,n) ∩ M`, so the target is
connected.

### First missing theorem

The closure equality requires density of hyperbolic parameters in every
relevant part of the boundary, and the incidence graph need not be connected
without a complete parabolic landing theory. Density of hyperbolicity is not
available in the required generality. The straddling region may contain
non-hyperbolic boundary continua not reached by the proposed union.

### Lean formalization

No hyperbolic-component object, structural-stability map, or boundary-density
theorem is defined. Existing `MandelbrotSet` connectedness cannot be refined
to this local component statement.

### Revision

This yields a conditional proof on a hyperbolic/density hypothesis, not an
axiom-free discharge.

## Attempt 7/10 — external-ray incidence correspondence

### Proposed proof

Let `E` be the incidence space of pairs `(c',θ)` for which the external ray
of angle `θ` lands at `c'` and lies on the boundary of the relevant parameter
piece. The angle interval corresponding to the Green level is connected.
The projection `E → ℂ` has image `A(c,n) ∩ M`, and the incidence space is
connected by the cyclic order of angles. Hence the image is connected.

### First missing theorem

Landing and continuous dependence of external rays at arbitrary Mandelbrot
boundary points are not available. The incidence space may fail to be a
single connected graph when landing is non-unique or inaccessible. Exact
identification of its projection with the full Green-sublevel intersection is
the classical parameter puzzle theorem.

### Lean formalization

The repository explicitly distinguishes the frozen Green model from genuine
ray/equipotential graph parapuzzles. No external-ray incidence type supplies
the required projection theorem. The existing near-infinity Böttcher family
does not extend to all boundary points.

### Revision

Use this route only after adding a genuine ray-landing and parameter-motion
interface; it cannot be inferred from the current source.

## Attempt 8/10 — categorical `K₀` localization and noncommutative descent

### Proposed proof

Associate to the pullback `P = A(c,n) ×_ℂ M` a stable category of finite
locally constant sheaves. A localization sequence for the complement and
Mayer--Vietoris descent identify

```text
K₀(P) ≅ K₀(A(c,n)) ×_{K₀(ℂ)} K₀(M).
```

Both factors have rank-one degree-zero `K₀`, so the pullback has rank one.
The finite-etale detector then implies `P` is connected.

### First missing theorem

Degree-zero `K₀` is not determined only by the ranks of the two factors:
restriction and gluing data can introduce extra idempotents. The claimed
Mayer--Vietoris equivalence requires an excision theorem for this exact
topological pullback. Efimov's abstract localizing invariants do not supply a
geometric comparison map for the Mandelbrot intersection.

### Lean formalization

The repository's `FiniteEtaleKZeroProbe` and descent structures explicitly
record restriction-surjectivity as a premise. `PacmanKTheory` and
`KTheoryLimitComparison` are interfaces, not an instantiated theorem for
`P`. The proposed calculation therefore stops at the existing conditional
excision theorem.

### Revision

Keep `K₀` as an obstruction detector and require geometric excision or
restriction-surjectivity as a separate input.

## Attempt 9/10 — universal family of polynomial-like restrictions

### Proposed proof

Construct a universal family `F : X → Y` of polynomial-like restrictions over
the full frozen source `A(c,n)`. Let `C ⊂ X` be the connectedness locus of
the filled Julia set. The family projection `p : C → ℂ` is proper and
surjective onto `A(c,n) ∩ M`. Since `C` is connected by a deformation of
the polynomial-like domains, its image is connected.

### First missing theorem

Connectedness of the universal family `C` does not follow from connectedness
of each fiber; the parameter base is exactly what must be proved connected.
Properness of `p` and exact surjectivity onto the literal `M` intersection
are also absent. Constructing them is the family-level straightening theorem.

### Lean formalization

The current `PacmanRealization` structure can express a family projection,
and `TopCatSurjectiveMorphism` proves its connected-image consequence. No
constructor from the existing dynamical data supplies `X`, `C`, or `p`.

### Revision

Treat the universal-family statement as a precise future specification of the
missing parameter realization.

## Attempt 10/10 — formal dependency and axiom-surface audit

### Proposed proof

Run a theorem-graph audit with the target axiom removed from the root imports.
Use all proved source connectedness, orbit-envelope, categorical pullback,
finite-etale, and Efimov interface lemmas. If one of them proves the target,
the axiom collector will no longer contain the frontier declaration.

### Formalization result

The available graph terminates at the conditional bridge

```lean
DouadyHubbardYoccozCategoricalTheorem →
  GreenSublevelIntersectionCategoricalData
```

and at equivalent finite-etale restriction-surjectivity criteria. No theorem
constructs either condition from the current base APIs. The root therefore
continues to require `MLC.green_sublevel_intersection_categorical`.

### Revision

The correct formal conclusion is not an independence theorem, but an exact
dependency report: all transport and equivalence lemmas are theorem-level,
while parameter-carving existence remains a project axiom.

## Round-7 conclusion and explicit axiom status

Incidence spaces, Hubbard trees, modulus estimates, semialgebraic stages,
monodromy, stability strata, external-ray incidence, `K₀` localization, and
universal polynomial-like families all require either an exact parameter map
or a new boundary/finite-stage theorem. None is derivable from the current
source connectivity and orbit-envelope results.

**AXIOM STATUS: NO AXIOM DISCHARGED.**

The checked root still uses exactly:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

No new axiom, `sorry`, or unproved identification of a model space with the
literal Mandelbrot intersection was introduced.
