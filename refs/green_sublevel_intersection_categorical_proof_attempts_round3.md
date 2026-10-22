# Third ten-iteration proof round for `MLC.green_sublevel_intersection_categorical`

This round deliberately avoids the ten mechanisms in the first two reports.
The target is unchanged:

```lean
∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
  ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
    ImageConnected
      (intersection (greenSublevelApproximation c n)
        mandelbrotApproximation)
```

Equivalently, with

```text
A(c,n) = {c' | G_c(c' - c) < 2^(-n)},
```

the remaining statement is

```text
A(c,n) ⊄ M  →  IsConnected (A(c,n) ∩ M).
```

For every attempt, the markdown argument is pushed to the first genuinely
unproved implication, then checked against the existing Lean interfaces. No
new assumption is silently promoted to an axiom.

## Attempt 1/10 — local connectedness from the frozen Green basis

### Proposed proof

The sets `A(c,n)` are connected neighborhoods of the translated filled Julia
set, and their intersection is `(c + K_c)`. Assume that
`A(c,n) ∩ M = U ⊔ V` is a separation. Since `M` is compact, choose disjoint
open sets `U'` and `V'` containing the two closed relative pieces. For every
point of `U` and `V`, use the nested Green sublevels to obtain a smaller
frozen neighborhood. Compactness gives a common level `m ≥ n`. Then
`A(c,m) ∩ M` is contained in one side of the separation. But every nested
Green neighborhood contains the translated connected core `c + K_c`, so it
cannot meet both sides. This contradicts the fact that `A(c,n)` meets both
components.

### First invalid step

The conclusion that a finer `A(c,m)` is contained in one side does not follow.
The nested sets shrink to `c + K_c`, not to a point, and the two components of
`A(c,n) ∩ M` may both accumulate on different parts of that translated
continuum. There is no theorem that the translated filled Julia set lies in a
single relative component of `M`.

### Lean formalization

The available theorem

```lean
iInter_green_sublevel_translate_eq_translate_filledJulia
```

formalizes exactly the obstruction. The existing nested-set API can prove
containment in an open neighborhood of `c + K_c`, but not containment in one
component of `A(c,n) ∩ M`. The attempted final step would require a new
parameter--dynamical component theorem.

### Revision

Replace point-shrinking by a genuine graph-cut or carving object whose limit
is the marked parameter. This is not a property of the current frozen tower.

## Attempt 2/10 — a purely planar full-continuum intersection theorem

### Proposed proof

Both `A(c,n)` and `M` are full connected planar sets. A full connected set
cannot be split by intersecting it with another full connected set unless the
second set has a bounded complementary component. Since the Green sublevel is
bounded by an equipotential and `M` has connected complement, their
intersection should therefore be connected.

### First invalid step

The planar assertion is false. Let `D` be an open disk. Take two small closed
disks `D₋` and `D₊` inside `D`, disjoint from one another, and join them by a
compact arc that leaves `D` and returns to the other disk while otherwise
staying outside `D`. The resulting compact connected set `C` has connected
complement after choosing the connecting arc as a simple outside bridge, but
`D ∩ C = D₋ ⊔ D₊` is disconnected. Thus connectedness and fullness of the
two ambient sets do not imply connectedness of their intersection.

### Lean formalization

The proposed general lemma cannot be stated honestly from the existing
topological hypotheses: Mathlib has no theorem with that conclusion because
the conclusion is false. The available facts

```lean
green_sublevel_translate_connected hc n
mandelbrot_set_connected
```

are insufficient to produce an `IsConnected.inter` proof.

### Revision

Any valid proof must use dynamical information specific to the pair
`(A(c,n), M)`, not only planar connectedness or fullness.

## Attempt 3/10 — connected finite-time outer stages

### Proposed proof

Use the compact outer approximation

```lean
outerOrbitSet N =
  {c | ‖c‖ ≤ 2 ∧ ∀ k ≤ N, ‖orbit c 0 k‖ ≤ 2}.
```

The identity

```text
M = ⋂ N, outerOrbitSet N
```

gives

```text
A(c,n) ∩ M = ⋂ N, (A(c,n) ∩ outerOrbitSet N).
```

If every finite-time intersection on the right is nonempty, compact, and
connected, the nested compact-intersection theorem proves the target.

### First missing theorem

The sets `outerOrbitSet N` are compact and decreasing, but their connectedness
is not proved and is not automatic. They are finite intersections of polynomial
lemniscates, and a preimage of a disk under a polynomial map can be
disconnected. Intersecting them with the connected set `A(c,n)` adds no general
connectedness theorem.

### Lean formalization

The generic limit transfer is already represented by
`TwoSidedSetApproximation.isPreconnected_of_outer`. Instantiating it requires
the exact premise

```lean
∀ N, IsPreconnected (A(c,n) ∩ outerOrbitSet N)
```

which is absent. The orbit identities therefore reduce the target to a
finite-time connectedness family but do not prove that family.

### Revision

Search for a dynamical or surgery construction of the finite-stage connected
sets; do not infer them from compactness.

## Attempt 4/10 — polynomial escape-coordinate lemniscates

### Proposed proof

For fixed `N`, package the finite orbit constraints into the holomorphic map

```text
E_N(c') = (f_{c'}(0), f_{c'}²(0), ..., f_{c'}^N(0)).
```

The outer stage is the inverse image of a product of closed disks under
`E_N`. Since the product of disks is convex and connected, and `E_N` is
holomorphic, the inverse image should be connected. Intersect with the
connected Green sublevel to obtain the finite-stage result from Attempt 3.

### First invalid step

Holomorphicity does not preserve connectedness under inverse image. Even a
single polynomial inverse image of a disk can have multiple components unless
one controls critical values and the relevant proper component. The
multi-coordinate map `E_N` has no injectivity or connected-fiber theorem in
the required region.

### Lean formalization

The attempted shape would require a theorem of the form

```lean
IsConnected T → IsConnected (E ⁻¹' T)
```

for the orbit map `E`, which is not a valid general theorem. Mathlib's
continuity and differentiability APIs provide the forward map but no
connected-preimage result. Adding a proper-map hypothesis still leaves the
connected-fiber and exact-component obligations unproved.

### Revision

Replace the inverse-image argument with a proper map on a specifically chosen
connected component, together with a parameter realization theorem.

## Attempt 5/10 — quasiconformal wringing deformation

### Proposed proof

For `c' ∈ A(c,n) ∩ M`, use the Böttcher coordinate to define a Beltrami
coefficient that straightens the external dynamics of `f_{c'}` to the
reference map `f_c`. Solve the Beltrami equation to obtain a quasiconformal
homeomorphism `h_{c'}`. Vary the coefficient linearly:

```text
μ_t = t μ_{c'}.
```

The measurable Riemann mapping theorem gives a continuous path of normalized
quadratic maps from `c` to `c'`, and every intermediate parameter remains in
the same Green sublevel and in `M`. Hence every point is path-connected to the
reference point, proving path-connectedness of the intersection.

### First missing theorem

The construction needs all of the following:

1. measurable solution and normalization for every `μ_t`;
2. continuous dependence of the normalized solution on `t` and `c'`;
3. preservation of the quadratic normalization;
4. the exact inequalities defining `A(c,n)`;
5. preservation of bounded critical orbit along the deformation.

The last item is not a formal consequence of quasiconformal conjugacy on the
basin; it is precisely the parameter-side connectedness assertion.

### Lean formalization

The repository has the conclusion interface
`SpaceHolomorphicCarvingData`, but no measurable Beltrami coefficient,
measurable Riemann mapping theorem, or normalized wringing map. The existing
space-holomorphic carving theorem can consume this construction but cannot
generate it.

### Revision

Use wringing as a concrete implementation plan for the missing carving datum,
not as a proof from the current axioms.

## Attempt 6/10 — Teichmüller space and a connected universal source

### Proposed proof

Let `T` be the normalized Teichmüller space of the basin with marked
quadratic dynamics. The admissible Beltrami coefficients form a star-shaped
connected set. The Bers/straightening projection

```text
π : T → ℂ
```

has image exactly `A(c,n) ∩ M`. Since `T` is connected and `π` is continuous,
the target is connected.

### First missing theorem

The image equality is not a formal property of Teichmüller space. One must
prove that every parameter in the literal Green-sublevel intersection has a
representative in the chosen marked Teichmüller slice, and that every
representative maps back into the same literal set. This is a
parameter--dynamical correspondence with the same strength as the carving
theorem.

### Lean formalization

No Teichmüller or Bers object in the repository has a map to
`TopCat.of ℂ`. The abstract `PacmanRealization` structure only records such
maps as input. Instantiating it here would introduce the missing realization
as a new assumption rather than discharge the target.

### Revision

If formalized later, use a connected Teichmüller source and prove an exact
image theorem before invoking `IsConnected.image`.

## Attempt 7/10 — `K₀` probes and extension across the frozen source

### Proposed proof

Assume that `A(c,n) ∩ M` is disconnected. Since it is nonempty, the
finite-etale detector gives a nonconstant

```lean
f : LocallyConstant (A(c,n) ∩ M) Bool.
```

Extend `f` along the inclusion into the connected source `A(c,n)`. A locally
constant Boolean function on the connected source is constant, contradicting
the nonconstancy of `f`. Therefore the intersection is connected.

### First invalid step

A locally constant function on a closed or arbitrary subspace does not
automatically extend to a locally constant function on the ambient space.
Such an extension exists exactly when the two clopen target pieces can be
separated by ambient clopen neighborhoods. For a connected source, that is
the missing connectedness statement in another form.

### Lean formalization

The repository proves

```lean
isConnected_iff_finiteEtaleKZeroProbeTrivial
```

and the pullback/excision criteria. It does not prove restriction-surjectivity
of probes from `A(c,n)` to `A(c,n) ∩ M`; the existing
`FiniteEtaleKZeroDescentData` records this as an explicit input. Consequently
the `K₀` proof is a valid conditional proof but not a discharge.

### Revision

Keep restriction-surjectivity as a diagnostic equivalent of the frontier, not
as a theorem inferred from Efimov's abstract `K`-theory interfaces.

## Attempt 8/10 — compact inverse limits with strong Mittag--Leffler data

### Proposed proof

Construct compact connected spaces `X_N` and surjective bonding maps
`X_{N+1} → X_N`, with a compatible map from the inverse limit
`lim X_N` to `A(c,n) ∩ M`. Strong Mittag--Leffler stabilization makes the
limit nonempty and preserves the relevant component probe. The target is the
continuous image of this connected inverse limit.

### First missing theorem

The current strong-Mittag--Leffler structures describe stabilization of
abstract ranges or `K`-theory values. They do not construct connected
parameter spaces `X_N`, bonding maps, or a map whose exact image is the
literal Green-sublevel intersection. The outer orbit stages are compact but
not known to be connected, and the frozen Green tower has the wrong limit.

### Lean formalization

The generic inverse-limit implication can be represented by the existing
`KTheoryLimitComparison`, `PacmanRealization`, and outer-approximation
interfaces. The exact-image map is a missing field, so Lean accepts only the
conditional theorem. No axiom-clean constructor from the existing
Mittag--Leffler data is available.

### Revision

Require geometric connected stages and an exact parameter projection in the
realization structure; abstract stabilization alone is insufficient.

## Attempt 9/10 — Green-gradient deformation and Morse theory

### Proposed proof

On the basin of infinity, the gradient flow of `G_c` retracts every sublevel
onto the filled Julia set. Translate this flow by `c`. If the flow preserves
the Mandelbrot condition, it gives a deformation retraction

```text
A(c,n) ∩ M  ↘  (c + K_c) ∩ M.
```

The endpoint is connected, so the intersection is connected.

### First invalid step

The flow is generated by the fixed dynamical function `G_c(c' - c)`, whereas
membership in `M` is determined by the critical orbit of the different map
`f_{c'}`. There is no reason for the flow line in the translated dynamical
plane to remain in `M`. Even the endpoint `(c + K_c) ∩ M` is not known to be a
single connected set.

### Lean formalization

The harmonic and Green-flow infrastructure proves statements inside the
dynamical basin. It has no `MapsTo` theorem for a flow into `MandelbrotSet`,
and no parameter identity relating the gradient of `G_c(c' - c)` to
`G_{c'}(c')`. The needed identity would be a parameter Green-function bridge
plus a monotonicity theorem, neither of which is present.

### Revision

A flow proof must first establish a genuine parameter Green potential and an
invariant deformation; that is a new parameter-plane theorem, not a
consequence of Route A.

## Attempt 10/10 — separating `K₀` probe plus analytic continuation

### Proposed proof

Assume a separation of `A(c,n) ∩ M`, and let a locally constant Boolean probe
distinguish its two components. Continue the probe along the Böttcher
parameter family from the marked dynamical source. Since the family is
holomorphic in the space variable and the source is connected, analytic
continuation forces the probe to be constant. Its endpoint values are
different, contradiction.

### First missing theorem

Analytic continuation applies to a function defined on a connected analytic
source. The Boolean probe is defined only on the parameter intersection; no
analytic continuation domain or map from the connected Green source to that
intersection has been constructed. Producing such a domain is exactly the
Douady--Hubbard carving map.

### Lean formalization

The existing theorem chain is the precise conditional version:

```lean
TopCatSurjectiveMorphism
  → isConnected_of_topCatSurjectiveMorphism
  → GreenSublevelIntersectionCategoricalData
```

and the finite-etale detector gives the equivalent probe formulation. There
is no axiom-clean theorem supplying the continuation map. The attempt
therefore reduces to the already formalized minimal frontier and adds no
new axiom.

### Revision

Use the probe/continuation argument as a characterization of what a future
phase--parameter realization must accomplish, not as an unconditional proof.

## Round-3 conclusion and axiom surface

The third round yields two useful reductions:

1. The two-sided orbit envelope reduces the target to connected finite-time
   intersections, but compactness and finite orbit constraints do not imply
   that connectedness.
2. Wringing, Teichmüller, strong Mittag--Leffler, and `K₀` probes all reduce to
   the same exact-image realization map already represented by
   `TopCatSurjectiveMorphism`.

No candidate proves the literal straddling statement from the current base
theorems. The checked root axiom surface remains:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

In particular, this round adds no replacement axiom, no `sorry`, and no
unverified claim that a classical Yoccoz or Efimov theorem already supplies
the exact full-Green-sublevel image.
