# Ten proof attempts for `MLC.green_sublevel_intersection_categorical`

This note records ten explicit attempts to discharge the remaining parameter
frontier. The target is

```lean
GreenSublevelIntersectionCategoricalData :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
      ImageConnected
        (intersection (greenSublevelApproximation c n)
          mandelbrotApproximation)
```

By `greenSublevelIntersectionCategoricalData_iff`, this is exactly the
set-theoretic assertion

```text
A(c,n) ⊄ M  →  IsConnected (A(c,n) ∩ M)

A(c,n) = {c' | G_c(c' - c) < 2^(-n)}.
```

The report distinguishes unconditional Lean proofs from conditional
reductions. No conditional reduction is promoted to a new root axiom.

## Attempt 1/10 — connectedness of the two factors

### Proposed proof

For `c ∈ M`, prove that `A(c,n)` is connected and use connectedness of `M`.
Then conclude that `A(c,n) ∩ M` is connected.

The first premise is available as
`green_sublevel_translate_connected`; connectedness of `M` is also an
independent consequence of the existing conditional root. The proposed final
step would be a general theorem

```text
IsConnected A → IsConnected M → IsConnected (A ∩ M).
```

### Formalization result

This final step is false in general. Two connected subsets of the plane can
have a disconnected intersection: a horizontal line segment and the unit
circle intersect in two points. Lean therefore has no valid theorem with the
proposed type. The attempt stops before using any MLC-specific information.

### Revision

The proof must use a parameter-specific phase--parameter relation, not merely
the connectedness of the two factors.

## Attempt 2/10 — decreasing compact outer approximations

### Proposed proof

Use the finite outer stages

```lean
O_N = {c : ‖c‖ ≤ 2 ∧ ∀ k ≤ N, ‖orbit c 0 k‖ ≤ 2}.
```

The Molecule characterization proves `⋂ N, O_N = M`; every `O_N` is compact.
For fixed `c,n`, define

```text
Q_N(c,n) = closure(A(c,n)) ∩ O_N.
```

If all nonempty `Q_N(c,n)` were preconnected and nested, the compact
intersection theorem would give connectedness of
`closure(A(c,n)) ∩ M`, and the open-sublevel target would follow if the
boundary portion were shown not to split the intersection.

### Formalization result

The orbit envelope itself is now formalized in
`Mlc/CategoricalMandelbrot.lean`:

```lean
iInter_outerOrbitSet_eq_set :
  (⋂ N, outerOrbitSet N) = MandelbrotSet
```

and `isCompact_outerOrbitSet` proves compactness of every outer stage.
The required preconnectedness of `Q_N(c,n)` is not available. In particular,
finite orbit constraints do not automatically preserve connectedness after
intersection with a Green sublevel.

### Revision

The outer system is a valid compact limit scaffold, but a new finite-stage
connectedness or carving theorem is required.

## Attempt 3/10 — increasing inner uniform-bound approximations

### Proposed proof

Use

```lean
I_N = {c | ∀ k, ‖orbit c 0 k‖ ≤ N}.
```

Every bounded critical orbit has a natural bound, so
`⋃ N, I_N = M`. If each `I_N ∩ A(c,n)` were connected and the intersections
shared a point, their increasing union would be connected and equal
`A(c,n) ∩ M`.

### Formalization result

The inner exhaustion and the generic increasing-union transfer theorem are
proved:

```lean
iUnion_innerOrbitSet_eq_set :
  (⋃ N, innerOrbitSet N) = MandelbrotSet

TwoSidedSetApproximation.isConnected_of_inner
```

The missing premise is exactly connectedness of every finite uniform-bound
intersection `I_N ∩ A(c,n)`. Boundedness of the orbit is an arithmetic
condition and supplies no phase--parameter connectivity.

### Revision

The inner system isolates a finite-stage target, but does not prove it.

## Attempt 4/10 — compactness converts a separation to finite orbit data

### Proposed proof

Assume `A(c,n) ∩ M` is disconnected. Separate it into two disjoint relatively
closed nonempty pieces. Since

```text
M = ⋂ N O_N
```

and `M` is compact, try to choose a finite `N` at which the separation is
already visible in `A(c,n) ∩ O_N`. If every such finite-stage set were
connected, this would contradict the separation.

### Formalization result

Compactness gives finite subcover and closed-intersection principles, but it
does not manufacture connectedness of `A(c,n) ∩ O_N`. The exact valid
conditional statement is the generic theorem

```lean
TwoSidedSetApproximation.isPreconnected_of_outer
```

which requires preconnectedness of every outer stage. The attempted
finite-detection implication therefore reduces to the same missing
finite-stage geometric theorem.

### Revision

Use compactness only after a genuine finite-stage phase--parameter theorem is
provided.

## Attempt 5/10 — Green-function monotonicity

### Proposed proof

Try to prove that the condition
`G_c(c' - c) < 2^(-n)` forces the critical orbit of `c'` to remain in a
connected family of bounded-orbit parameters. Then `A(c,n) ∩ M` would be a
sublevel or image of one connected dynamical set.

### Formalization result

The Green function in `A(c,n)` is the dynamical Green function for the fixed
map `f_c` evaluated at `c' - c`. Membership `c' ∈ M` is boundedness of the
critical orbit for the different map `f_{c'}`. No monotonicity or implication
between these two statements follows from the available Green identities.

The exact missing statement would have to identify the parameter condition
with an image of a dynamical locus. That is already the carving field in
`SpaceHolomorphicCarvingData`.

### Revision

Replace the nonexistent monotonicity lemma by an explicit phase--parameter
map with an exact image theorem.

## Attempt 6/10 — Böttcher coordinate and external-ray parametrization

### Proposed proof

Use the Böttcher coordinate to parametrize the equipotential
`G_c = 2^(-n)` and extend that parametrization across the part lying in `M`.
The image of the connected disk bounded by the equipotential would then be
`A(c,n) ∩ M`.

### Formalization result

The Böttcher construction available in the repository is a near-infinity
construction on the basin of infinity. Extending it through the Julia set and
identifying the image with the Mandelbrot intersection requires precisely the
boundary landing and parameter realization theorem that is absent. A
continuous extension over the relevant boundary would already encode a
substantial local-connectivity/holomorphic-motion assertion.

The route therefore cannot be formalized without adding the missing analytic
theorem as an explicit hypothesis.

### Revision

State the required extension as a structured carving datum rather than
claiming it follows from the local Böttcher API.

## Attempt 7/10 — classical Yoccoz parapuzzle theorem

### Proposed proof

Invoke Yoccoz's shrinking theorem and the phase--parameter correspondence for
finitely renormalizable parameters. This should give connected parameter
pieces and hence the target intersection.

### Formalization result

The current `ParaPuzzlePieceAt` is a translate of a connected component of the
**full** Green sublevel. The proved identity

```lean
iInter_green_sublevel_translate_eq_translate_filledJulia
```

shows that its full tower has intersection `c + K_c`, not `{c}`. It is not the
graph-cut ray/equipotential parapuzzle used in the classical Yoccoz proof.
The dependency's `yoccoz_theorem` therefore cannot be applied as a theorem
about the present `A(c,n) ∩ M`.

### Revision

Either formalize genuine graph-cut parapuzzles, or keep the current target and
prove a new full-Green-sublevel carving theorem. The latter is the smaller
interface and is used below.

## Attempt 8/10 — finite-etale `K₀` component detection

### Proposed proof

A nonempty set is connected iff every locally constant `Bool`-valued probe is
constant. Apply this to `A(c,n) ∩ M`; prove every probe descends from the
connected source `A(c,n)` by a strong Mittag--Leffler/excision argument.

### Formalization result

The component detector is proved in
`Mlc/EfimovCategoricalBridge.lean`:

```lean
isConnected_iff_finiteEtaleKZeroProbeTrivial
```

The target-specific restriction-surjectivity and pullback-excision
formulations are also proved equivalent to the frontier. This is an exact
`K₀`-shadow reformulation, not a proof: the required restriction-surjectivity
is equivalent to the original connectedness statement.

### Revision

Use the detector to specify the missing excision theorem, but do not infer
excision from abstract Efimov data without a conservative realization.

## Attempt 9/10 — regular epimorphism in `TopCat`

### Proposed proof

Construct a surjective continuous morphism

```text
A(c,n) ⟶ A(c,n) ∩ M
```

from the connected source. A surjective image of a connected space is
connected, so the target follows categorically.

### Formalization result

This implication is fully formalized:

```lean
isConnected_of_topCatSurjectiveMorphism
isConnected_greenSublevelIntersection_of_douadyHubbardYoccozCarving
greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz
```

The existence of the morphism is not formalized. The
`image_eq` field in `SpaceHolomorphicCarvingData` is exactly the missing
phase--parameter theorem, so replacing the frontier axiom by its existence
would only rename the same open obligation.

### Revision

Keep the categorical theorem as a proved reduction and expose the analytic
existence field explicitly.

## Attempt 10/10 — two-sided outer/inner realization comparison

### Proposed proof

Use the two-sided orbit envelope:

```text
⋃ N I_N = M = ⋂ N O_N.
```

For a fixed Green level, construct a connected dynamical realization that
lands in every outer stage and eventually lands in an inner stage. Compactness
of the outer system and directedness of the inner system would identify its
image with `A(c,n) ∩ M`, after which the connected-image theorem would finish.

### Formalization result

The two-sided orbit envelope, its exact limit identities, compact outer
stages, sandwich morphisms, and generic connectedness transfer lemmas are now
proved in `Mlc/CategoricalMandelbrot.lean`. What remains is the realization
comparison:

1. a connected source mapping into every finite outer relative piece;
2. compatibility of those maps in the inverse system;
3. eventual landing in an inner uniform-bound stage;
4. equality of the realized image with `A(c,n) ∩ M`.

Items 1--4 are not consequences of bounded-orbit definitions. They are a
phase--parameter/carving theorem in a different presentation.

### Final rigorous conclusion

The strongest unconditional Lean result available after all ten iterations is
the connected-image implication under the explicit carving datum. The
remaining axiom
`MLC.green_sublevel_intersection_categorical` is not discharged. The exact
smallest missing theorem is one of the equivalent statements:

```lean
Nonempty (DouadyHubbardYoccozCategoricalCarvingData c n)
```

for every straddling `(c,n)`, or an equivalent conservative
finite-stage/outer-inner realization theorem.

No new project axiom was introduced, and no equivalent axiom was relabeled as
a proof.
