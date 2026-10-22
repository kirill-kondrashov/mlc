# Up-to-100 proof/formalization attempts for `MLC.green_sublevel_intersection_categorical`

This report records one hundred bounded attempts, grouped into ten batches.
Every attempt has the same three stages:

1. a proposed markdown proof;
2. the corresponding Lean formalization shape;
3. a revision at the first missing or invalid implication.

The target is

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

the set-level statement is `A(c,n) ⊄ M → IsConnected (A(c,n) ∩ M)`.
The existing theorem

```lean
iInter_green_sublevel_translate_eq_translate_filledJulia
```

is used throughout: the full frozen Green tower converges to
`(fun z => z + c) '' K c`, not to a single parameter. Thus a proof may not
silently replace the current source by a classical graph-cut parapuzzle.

## Batch A — planar topology and continuum theory

### Attempt 1/100 — intersection of full continua

**Markdown proof.** `A(c,n)` is a connected full planar neighborhood and `M`
is a connected full continuum. A separator for `A(c,n) ∩ M` would create a
bounded complementary component of one of these full sets, impossible.

**Lean.** The available hypotheses are `green_sublevel_translate_connected`
and `mandelbrot_set_connected`; no theorem derives connectedness of an
intersection from those hypotheses.

**Revision.** The planar implication is false: a connected bridge outside a
disk can join two compact pieces inside the disk. Fullness alone is
insufficient.

### Attempt 2/100 — boundary bumping

**Markdown proof.** If `A(c,n) ∩ M` has two components, boundary bumping says
each component meets the boundary of `A(c,n)`. The equipotential boundary is
connected, so the two components must meet and therefore coincide.

**Lean.** Boundary-bumping theorems only assert contact with a boundary, not
that different component closures intersect. No theorem identifies the
closures of the two relative components on the equipotential.

**Revision.** Supply a parameter-side landing or carving map on the boundary;
the connected equipotential alone does not glue the components.

### Attempt 3/100 — irreducible continuum

**Markdown proof.** Choose a minimal subcontinuum of `M` joining two points of
the intersection. Its irreducibility forces every separating continuum in
`A(c,n) \ M` to meet the minimal continuum, a contradiction.

**Lean.** No irreducible subcontinuum joining arbitrary points of `M` is
constructed, and minimality does not imply that the subcontinuum stays inside
`A(c,n)`.

**Revision.** An irreducible-continuum argument requires a new theorem that
the relevant minimal continuum is contained in the frozen Green neighborhood.

### Attempt 4/100 — unicoherence

**Markdown proof.** Decompose `M` into `M ∩ A(c,n)` and `M \ interior(A(c,n))`.
If `M` is unicoherent, the intersection of the two connected closed pieces
is connected. Hence `M ∩ A(c,n)` is connected.

**Lean.** The second piece is not proved connected, and `M` is not equipped
with a formal unicoherence theorem. Also `A(c,n)` is open, so the required
closed decomposition needs a boundary thickening.

**Revision.** Unicoherence would be a substantial new property of the
Mandelbrot continuum, not a consequence of its connectedness.

### Attempt 5/100 — dendroid structure

**Markdown proof.** If `M` were a dendroid, the unique arc between any two
points of `M ∩ A(c,n)` would lie in the connected Green neighborhood, so the
intersection would be arc-connected.

**Lean.** No dendroid or unique-arc structure for `M` is available, and MLC
does not imply that the Mandelbrot set is a dendrite.

**Revision.** This route changes the target to a stronger unproved structural
conjecture.

### Attempt 6/100 — chainability

**Markdown proof.** Cover `M` by a chain of arbitrarily small linked
continua. Intersect the chain with `A(c,n)`; linked consecutive members keep
the intersection connected.

**Lean.** Chainability of `M` is not known and the intersection of a linked
continuum with an open set need not remain nonempty or linked.

**Revision.** A chain cover must be built from parameter puzzle pieces; that is
again the missing parameter connectivity theorem.

### Attempt 7/100 — Moore decomposition

**Markdown proof.** Decompose the plane into the components of `M` outside
`A(c,n)` and apply Moore's theorem to obtain a planar quotient. The image of
the connected source Green sublevel is a disk; its inverse image in the
quotient is `A(c,n) ∩ M`, hence connected.

**Lean.** No upper-semicontinuous decomposition or quotient identification
with the literal Mandelbrot subspace is present.

**Revision.** Moore's theorem can construct a model quotient only after the
decomposition and exact projection map are supplied.

### Attempt 8/100 — Alexander separation

**Markdown proof.** A disconnected compact intersection has a separating
continuum. Alexander duality converts it into nontrivial first cohomology of
the complement. The complement of the full Mandelbrot set in the Green disk
has trivial first cohomology, contradiction.

**Lean.** The required relative compactification and complement cohomology
calculation are absent; the asserted cohomology vanishing is not implied by
connectedness of the complement.

**Revision.** Duality is a diagnostic for a separator, not a proof that no
separator exists.

### Attempt 9/100 — plane separation by crosscuts

**Markdown proof.** A separation gives a crosscut of the Green disk in the
complement of `M`. External rays continue the crosscut to infinity, where
the complement is connected, so the crosscut cannot separate two pieces.

**Lean.** No theorem extends an arbitrary parameter crosscut to an external
ray while avoiding `M`; the required extension is a parameter landing
correspondence.

**Revision.** Restrict crosscut arguments to genuine graph-cut parapuzzles.

### Attempt 10/100 — boundary accessibility

**Markdown proof.** Every component of `M ∩ A(c,n)` has an accessible point on
the equipotential. Cyclic ordering of accessible points on the Jordan
boundary gives an arc in `M` between any two components.

**Lean.** Accessibility and the required boundary arc in `M` are not proved.
The equipotential is dynamical, while the endpoint condition is parameter
theoretic.

**Revision.** Add a boundary-motion theorem with exact image before using
accessibility.

## Batch B — potential theory and PDE

### Attempt 11/100 — parameter Green zero set

**Markdown proof.** Define `G_M(c') = G_{c'}(c')`. The set `M` is `G_M = 0`.
The sum `G_M + λ G_c(c'-c)` has a minimum on the compact closure of the
straddling piece; the minimum principle forces its zero set to connect the
two components.

**Lean.** There is no parameter Green function or zero-set minimum theorem.
Subharmonic minimum principles do not imply connectedness of zero sets.

**Revision.** A parameter Green identity is a bridge, not a completed proof.

### Attempt 12/100 — convexity of a potential sublevel

**Markdown proof.** The Laplacian of `G_c` is nonnegative, so its sublevels
are convex in the parameter translation. Intersecting with the continuum
`M` preserves connectedness.

**Lean.** Subharmonic functions have no convex sublevel theorem, and the
intersection assertion is false for arbitrary convex domains and continua.

**Revision.** Replace convexity by a genuine parameter-specific monotonicity
theorem, which is not present.

### Attempt 13/100 — obstacle problem

**Markdown proof.** Treat `M` as the coincidence set of an obstacle problem
with obstacle zero and `G_c(c'-c)` as the obstacle gap. Coincidence sets of
planar obstacles are connected in the straddling disk.

**Lean.** No obstacle problem or coincidence-set regularity is formalized;
the claimed connectedness is false for general obstacles.

**Revision.** An obstacle formulation would require proving special
monotonicity of the Mandelbrot obstacle.

### Attempt 14/100 — free-boundary regularity

**Markdown proof.** The equipotential is smooth and intersects the free
boundary `∂M` transversely. A transverse intersection cannot create two
components inside a disk containing the marked point.

**Lean.** No regularity or transversality of `∂M` is known; MLC concerns
precisely the lack of such smooth boundary control.

**Revision.** Transversality must be a new hypothesis, not inferred from the
dynamical equipotential.

### Attempt 15/100 — harmonic measure

**Markdown proof.** Assign harmonic measure in `A(c,n) \ M` to each component
of `M ∩ A(c,n)`. The measure is constant on the equipotential and the
maximum principle forces all component masses to merge.

**Lean.** Harmonic measure for the parameter complement and boundary values
on `∂M` are not available. The dynamical harmonicity theorem applies to
`G_c` outside `K_c`, not to the parameter complement of `M`.

**Revision.** Require a parameter Dirichlet problem with boundary data from a
carving theorem.

### Attempt 16/100 — gradient-flow deformation

**Markdown proof.** The gradient flow of `G_c(c'-c)` retracts `A(c,n)` onto
`c + K_c`. If the flow preserves `M`, it retracts the intersection onto a
connected set.

**Lean.** No `MapsTo` theorem says that the fixed dynamical flow preserves
Mandelbrot membership; even the endpoint intersection is not known connected.

**Revision.** The needed invariant flow is an exact parameter realization.

### Attempt 17/100 — obstacle-gradient flow

**Markdown proof.** Replace the fixed Green flow by the gradient of
`G_M + G_c`. The zero obstacle makes `M` invariant and the combined flow
contracts every straddling piece to `c`.

**Lean.** `G_M` is not defined, and no parameter gradient flow or invariance
theorem exists.

**Revision.** This is a speculative PDE program, not a formal proof.

### Attempt 18/100 — Ahlfors metric on the parameter complement

**Markdown proof.** Put a complete negative-curvature metric on
`ℂ \ M`. A separator in `A(c,n) \ M` would yield a short geodesic violating
the Schwarz--Pick bound from the dynamical Green disk.

**Lean.** The existing ultrahyperbolic metric concerns `ℂ \ {0,1}` and is
incomplete at punctures; no complete metric on `ℂ \ M` or comparison map is
available.

**Revision.** Metric contraction still requires a phase--parameter map.

### Attempt 19/100 — free-boundary capacity

**Markdown proof.** A disconnected intersection creates two positive-capacity
boundary components. Capacity monotonicity of the Green equipotential bounds
their sum by the capacity of one component, contradiction.

**Lean.** No capacity computation for `M ∩ A(c,n)` or additivity estimate is
formalized; positive capacity does not by itself contradict disconnection.

**Revision.** Capacity can quantify a separator only after it is constructed.

### Attempt 20/100 — potential-theoretic uniqueness

**Markdown proof.** Solve a Dirichlet problem with boundary values `0` on
`M ∩ A(c,n)` and `1` on the equipotential. Uniqueness forces the solution to
be the fixed Green function, whose connected level sets imply the target.

**Lean.** Boundary data on a disconnected relative set and uniqueness on the
punctured domain do not identify the solution with `G_c`; no parameter
Dirichlet comparison is available.

**Revision.** This reduces to a missing parameter boundary-value theorem.

## Batch C — complex dynamics and renormalization

### Attempt 21/100 — Hubbard-tree approximation

**Markdown proof.** Approximate every parameter in the straddling set by
postcritically finite parameters. Their Hubbard trees are finite and
connected; regulated arcs join all points inside the Green piece. Take a
Hausdorff limit of the trees to obtain a connected subset of `M ∩ A(c,n)`
containing every point.

**Lean.** Postcritically finite density in the required relative set and
Hausdorff convergence of regulated arcs are missing.

**Revision.** Formalize a finite postcritically finite stratum only; the
limit theorem is the frontier.

### Attempt 22/100 — puzzle pullback components

**Markdown proof.** Pull back a connected level-`n` puzzle piece under the
quadratic map. Every pullback component meeting the critical orbit is
connected and maps onto the previous piece. Inductively the parameter
intersection is one such component.

**Lean.** The current parameter piece is a frozen full Green sublevel, not a
graph-cut pullback. No parameter pullback map or component selection exists.

**Revision.** Introduce genuine graph-cut parapuzzles before using pullback
component induction.

### Attempt 23/100 — renormalization depth induction

**Markdown proof.** Induct on the number of renormalizations. At each
renormalization, straightening maps the parameter piece to a lower-depth
Mandelbrot copy, whose intersection is connected by induction. Satellite
decorations attach along connected root arcs, preserving connectedness.

**Lean.** The residual virtual near-Molecule branch has no finite induction
depth, and the straightening/decorations have no exact image theorem.

**Revision.** This only proves conditional finite renormalization statements.

### Attempt 24/100 — satellite root attachment

**Markdown proof.** Every satellite copy intersects the parent copy in its
root point or root arc. A finite chain of satellite copies joining the
straddling piece to the main copy gives a connected union.

**Lean.** Root intersection and the chain covering all of `M ∩ A(c,n)` are
not formalized; arbitrary non-locally-connected boundary pieces may not be
captured by finite satellite chains.

**Revision.** Add a complete satellite decomposition theorem, which is beyond
the current base axioms.

### Attempt 25/100 — primitive copy straightening

**Markdown proof.** A primitive polynomial-like restriction has a continuous
straightening map with connected connectedness locus. The straddling
intersection is the image of that locus under the parameter embedding.

**Lean.** The family-level straightening map, its continuity, and exact
parameter embedding are absent.

**Revision.** Record the map as `PacmanRealization` data; it is not generated
by the existing renormalization interfaces.

### Attempt 26/100 — near-neutral parabolic implosion

**Markdown proof.** In the near-neutral case, Ecalle cylinders identify all
parameters in the same Green piece through a connected horn-map parameter.
The horn map varies continuously and its image is the full intersection.

**Lean.** No Ecalle-cylinder or horn-map construction exists, and exact image
coverage at irrational neutral parameters is not available.

**Revision.** This route requires new parabolic parameter theory.

### Attempt 27/100 — no-wandering-domain pullback

**Markdown proof.** A disconnected intersection would create two disjoint
parameter domains carrying the same bounded critical itinerary. Pulling them
back produces a wandering domain in the dynamical family, contradicting the
no-wandering-domain theorem.

**Lean.** A parameter component is not a dynamical Fatou domain; no map sends
the alleged parameter domains to wandering dynamical domains.

**Revision.** The analogy cannot replace a parameter realization map.

### Attempt 28/100 — critical portrait monotonicity

**Markdown proof.** Order the critical portraits by inclusion of finite
itineraries. The set of portraits compatible with a fixed Green level is an
interval in the portrait order. The realization map from portraits to
parameters has connected fibers, so its image is connected.

**Lean.** No global portrait order or realization map is available for
complex quadratic parameters; finite itinerary inclusion is not a total order.

**Revision.** Restrict to the real quadratic slice, where this is a different
theorem from the complex frontier.

### Attempt 29/100 — Hubbard lamination monotonicity

**Markdown proof.** Lamination leaves corresponding to the frozen Green
sublevel form a noncrossing family. Their quotient is an interval, and the
parameter realization is monotone. The inverse image of an interval under a
monotone map is connected.

**Lean.** The complex lamination quotient and monotone realization to the
literal `M` are not defined; proving them is a form of MLC.

**Revision.** Treat lamination monotonicity as an explicit future axiom-free
target, not as existing infrastructure.

### Attempt 30/100 — a priori bounds force one component

**Markdown proof.** If two components survive at every depth, the annulus
between them has modulus tending to zero. Dudko--Lyubich a priori bounds give
a uniform positive modulus in every renormalization regime, contradiction.

**Lean.** The residual open virtual near-Molecule axiom covers only the
specified open program. It does not provide a modulus estimate for arbitrary
components of the frozen parameter intersection.

**Revision.** A priori bounds can support a genuine puzzle proof after the
parameter puzzle is constructed.

## Batch D — quasiconformal, Teichmüller, and Böttcher realization

### Attempt 31/100 — wringing path

**Markdown proof.** Linearly interpolate the external Beltrami coefficient
between two parameters in the same Green piece. Solve the Beltrami equation,
normalize the result, and obtain a path entirely in `A(c,n) ∩ M`.

**Lean.** Measurable Riemann mapping, parameter dependence, and bounded-orbit
preservation are absent.

**Revision.** Wringing is a candidate constructor for
`SpaceHolomorphicCarvingData`, not a theorem from current axioms.

### Attempt 32/100 — Teichmüller geodesic

**Markdown proof.** Join two marked quadratic structures by the unique
Teichmüller geodesic. Its normalized quadratic projection remains in the
same Green sublevel and in the connectedness locus.

**Lean.** No Teichmüller space or projection is formalized, and the
projection-preservation claim is exactly the missing parameter theorem.

**Revision.** Require an exact image and `MapsTo` field for the geodesic
projection.

### Attempt 33/100 — Bers slice

**Markdown proof.** Embed the marked family into a connected Bers slice. The
Mandelbrot intersection is the image of a connected slice of the Bers
embedding, hence connected.

**Lean.** No Bers embedding or identification of its image with the literal
quadratic parameter set exists.

**Revision.** This is a model-space argument until the identification is
proved.

### Attempt 34/100 — Beltrami coefficient compactness

**Markdown proof.** The unit ball of Beltrami coefficients is weak-* compact
and connected. The normalized solution map is continuous, and its image is
exactly the target intersection.

**Lean.** Weak-* compactness and the normalized solution map are unavailable;
exact image is not implied by compactness.

**Revision.** Add the normalized solution map as geometric input.

### Attempt 35/100 — holomorphic motion and λ-lemma

**Markdown proof.** Construct a nontrivial holomorphic motion of the
equipotential boundary. The λ-lemma extends it to a motion of the disk, whose
time slice maps the connected frozen source onto `A(c,n) ∩ M`.

**Lean.** The λ-lemma transport is formalized conditionally, but the actual
motion and exact time-slice image are not.

**Revision.** The missing motion is precisely the current carving frontier.

### Attempt 36/100 — Słodkowski extension

**Markdown proof.** Extend the boundary motion to the sphere by Słodkowski.
Restrict the extension to the Green sublevel; its image is the parameter
intersection and is connected.

**Lean.** The extension theorem is an interface only; no boundary motion with
the required `MapsTo` and `image_eq` fields exists.

**Revision.** Keep the theorem conditional on `SpaceHolomorphicMotion`.

### Attempt 37/100 — Hartogs joint analyticity

**Markdown proof.** The Böttcher coordinate is separately holomorphic in
parameter and space and jointly continuous. Hartogs' theorem gives joint
holomorphy. The inverse is jointly holomorphic and supplies the carving.

**Lean.** Joint analyticity near infinity is partially formalized, but
basin-wide extension, inverse branch gluing, and exact parameter image remain
unproved.

**Revision.** Complete the basin extension before using Hartogs for the
frontier.

### Attempt 38/100 — inverse Böttcher branch

**Markdown proof.** Use the analytic inverse near infinity and pull it back
through escape times. Compatible roots define a global inverse
`Φ_c^{-1}(ω)`. The equipotential parameterization is holomorphic in `ω`,
therefore its image is connected.

**Lean.** Root compatibility across changing escape times and boundary
continuation are missing. Holomorphy of the source parameterization alone
does not identify its image with `M ∩ A`.

**Revision.** Add exact image equality as a separate theorem.

### Attempt 39/100 — phase-parameter identity

**Markdown proof.** Prove `G_M(c') = G_{c'}(c')` and identify
`G_c(c'-c)` with the phase Green function under the Böttcher phase map.
Then `M ∩ A` is the image of a connected phase sublevel.

**Lean.** Neither the parameter Green identity nor the phase identity is
available; the latter is the Douady--Hubbard correspondence.

**Revision.** Formalize the identities as bridge lemmas before attempting
connectedness.

### Attempt 40/100 — quasiconformal boundary extension

**Markdown proof.** A quasiconformal homeomorphism of the external disk
extends continuously to the equipotential Jordan boundary. Its image of the
closed disk is a continuum containing the full intersection.

**Lean.** Extension to the relevant parameter boundary and equality rather
than containment are absent.

**Revision.** Containment cannot replace `image_eq` in the carving structure.

## Batch E — finite stages and computational approximation

### Attempt 41/100 — connected outer stages

**Markdown proof.** Each finite outer stage is a finite intersection of
non-escape disks. Since the first stage is a disk and each later condition is
a connected pullback, induction gives connectedness.

**Lean.** Polynomial preimages of disks need not be connected; no connected
pullback theorem applies to the orbit constraints.

**Revision.** Prove connectedness of each stage as an independent finite
parameter theorem.

### Attempt 42/100 — connected inner stages

**Markdown proof.** Inner stages impose a uniform orbit bound. Uniformly
bounded critical orbits form a connected basin of the parameter family, so
each inner stage is connected. Their increasing union is `M`.

**Lean.** Uniform boundedness is a countable conjunction of inequalities and
is not known to define a connected set. The inner approximation theorem only
proves the union identity.

**Revision.** The union identity does not provide connected stages.

### Attempt 43/100 — semialgebraic cylindrical decomposition

**Markdown proof.** Every finite orbit stage is semialgebraic. Cylindrical
decomposition yields cells; prove the cell adjacency graph is connected by
following the critical orbit constraints from the marked cell.

**Lean.** No semialgebraic cell API or adjacency theorem is imported, and the
claimed adjacency is not automatic.

**Revision.** Use this only for explicit low-depth computations.

### Attempt 44/100 — polynomial lemniscate connectedness

**Markdown proof.** Each finite condition is a polynomial lemniscate. The
critical value lies inside the disk, so the lemniscate component containing
the critical parameter is the whole lemniscate.

**Lean.** The critical-value inclusion is not established for all orbit
polynomials, and even one polynomial lemniscate may have multiple components.

**Revision.** Need a critical-value separation theorem for every finite stage.

### Attempt 45/100 — orbit constraint graph

**Markdown proof.** Build a graph whose vertices are finite orbit cells and
whose edges are shared constraint boundaries. The graph is connected because
all cells can be reduced to the zero-orbit cell by deleting constraints.

**Lean.** Deleting an orbit constraint can merge cells but does not provide a
path in the original constrained set. No cell graph is formalized.

**Revision.** Add explicit path constructions between cells; this is not a
consequence of monotonicity of constraints.

### Attempt 46/100 — SAT-style connectedness certificate

**Markdown proof.** A disconnected finite stage admits a finite Boolean
certificate separating its cells. Solve the finite polynomial inequalities
along the certificate and derive an unsatisfiable sign pattern.

**Lean.** No general CAD/SAT certificate for complex polynomial inequalities
is present, and no unsatisfiability theorem for all depths is known.

**Revision.** Computational certificates can verify selected stages, not the
unbounded theorem.

### Attempt 47/100 — finite detection of a clopen separator

**Markdown proof.** If the compact target is disconnected, a clopen separator
has positive distance between its two pieces. Outer approximation converges
to `M`, so some finite stage preserves the separator. Contradict finite-stage
connectedness.

**Lean.** The compact finite-detection argument is valid conditionally, but
finite-stage connectedness is absent.

**Revision.** This yields a useful reduction, not a discharge.

### Attempt 48/100 — nerve of orbit sublevel sets

**Markdown proof.** Cover the target by the sets corresponding to individual
orbit constraints. Every finite intersection is connected and the nerve is a
simplex, so the nerve theorem gives connectedness.

**Lean.** Individual constraint intersections are not proved connected and
the cover is by closed conditions, not a good open cover.

**Revision.** Supply a good cover with connected finite intersections.

### Attempt 49/100 — inverse limit of finite connected models

**Markdown proof.** Replace each outer stage by its connected component
containing `c`. Surjective bonding maps give a connected inverse limit whose
projection is the full target.

**Lean.** There is no theorem that the selected components contain every
point of `M ∩ A`; the projection need not be surjective.

**Revision.** Surjectivity of the component projection is the missing
parameter connectivity statement.

### Attempt 50/100 — pro-object of finite constraints

**Markdown proof.** Regard the finite orbit stages as a pro-object. Strong
Mittag--Leffler stabilization makes its limit connected because all eventual
ranges stabilize to the marked component.

**Lean.** Existing Mittag--Leffler data concern abstract ranges, not
connected components of the literal orbit stages. Stabilization of ranges
does not imply geometric connectedness.

**Revision.** Add geometric connected-stage and connected-fiber fields.

## Batch F — categorical descent and `π₀`

### Attempt 51/100 — `π₀` of the pullback

**Markdown proof.** Compute
`π₀(A ×_ℂ M) = π₀(A) ×_{π₀(ℂ)} π₀(M)`. Both factors are singletons,
so the pullback is connected.

**Lean.** `π₀` does not preserve arbitrary pullbacks in `TopCat`; the claimed
formula is false without fibration or open-map hypotheses.

**Revision.** Add a connected-fiber base-change theorem, which is equivalent
to supplying a carving map.

### Attempt 52/100 — regular epimorphism

**Markdown proof.** The inclusion of `M` induces a regular epimorphism from
the connected Green source onto the pullback. Regular epimorphic images of
connected objects are connected.

**Lean.** The regular epimorphism is not constructed. The existing
`TopCatSurjectiveMorphism` theorem proves only the consequence once its map
is supplied.

**Revision.** Keep the regular-epi statement as the minimal categorical
frontier.

### Attempt 53/100 — coequalizer of a connected relation

**Markdown proof.** Identify the intersection as the coequalizer of the two
projections of a connected equivalence relation on `A(c,n)`. Coequalizers
preserve connectedness.

**Lean.** No relation or coequalizer comparison with the literal target is
available.

**Revision.** Exact quotient identification remains a missing field.

### Attempt 54/100 — effective descent

**Markdown proof.** Cover the pullback by connected open charts with connected
overlaps. Effective descent glues their connected objects, so the pullback is
connected.

**Lean.** The charts, overlaps, and descent datum are not constructed.

**Revision.** Require a geometric cover before invoking categorical descent.

### Attempt 55/100 — locale complemented opens

**Markdown proof.** A disconnected space has a nontrivial complemented
element in its frame of opens. Pull it back to the connected source; the
source frame has no such element, contradiction.

**Lean.** Clopen subsets of a subspace do not generally extend to clopen
subsets of the ambient source. The extension is exactly the missing probe
surjectivity.

**Revision.** Locale language reformulates, but does not solve, the problem.

### Attempt 56/100 — component cosheaf

**Markdown proof.** Components form a cosheaf on the Green source. The source
has one global component and stalkwise connectedness of the target forces one
global target component.

**Lean.** No component cosheaf or effective cosheaf descent is formalized.

**Revision.** Add probe-surjective descent as an explicit hypothesis.

### Attempt 57/100 — sheaf of Boolean probes

**Markdown proof.** A separating locally constant Boolean probe on the target
extends to the source sheaf. The source is connected, so the extension is
constant, contradiction.

**Lean.** The extension map on locally constant functions is not surjective;
the existing finite-etale theorem makes this exact obstruction explicit.

**Revision.** Prove restriction-surjectivity by geometry, not by sheaf
formalism alone.

### Attempt 58/100 — Kan extension of components

**Markdown proof.** Left Kan extend the component functor from the target
inclusion to the connected source. Colimits of singleton component sets are
singletons, so the target has one component.

**Lean.** No Kan-extension object is tied to `TopCat` subspaces here, and the
extension values are not known to be singleton.

**Revision.** The needed Kan-extension exactness is another form of carving.

### Attempt 59/100 — infinity-categorical limit

**Markdown proof.** Express the Green/Mandelbrot intersection as a homotopy
pullback of connected objects in an infinity-category of spaces. A
homotopy-cartesian square with connected fibers has connected total object.

**Lean.** The current `TopCat` pullback is an ordinary set-theoretic pullback;
no homotopy-cartesian or connected-fiber comparison is present.

**Revision.** An infinity-categorical formulation still needs geometric
connected-fiber data.

### Attempt 60/100 — stable localization

**Markdown proof.** A localization sequence for the complement gives an exact
sequence on stable `K`-theory. Vanishing of the degree-zero reduced term
forces connectedness of the pullback.

**Lean.** Stable localization is represented only by interfaces and no
specific geometric sequence is instantiated.

**Revision.** Require an actual excision theorem for the parameter pair.

## Batch G — homology, shape, and invariant refinements

### Attempt 61/100 — finite-etale detector directly

**Markdown proof.** If the target is disconnected, a nonconstant
`LocallyConstant S Bool` exists. Restricting it to the connected Green source
makes it constant, contradiction.

**Lean.** Restriction is from the source to the target, and a function on the
target does not automatically extend to the source. The direction required
for the contradiction is unavailable.

**Revision.** Prove restriction-surjectivity or construct a surjective map.

### Attempt 62/100 — `K₀` rank calculation

**Markdown proof.** Both `A(c,n)` and `M` have rank-one degree-zero `K₀`.
Excision gives rank one for their pullback, hence connectedness.

**Lean.** Rank-one `K₀` does not imply rank-one `K₀` after an arbitrary
pullback; the excision map is missing.

**Revision.** Add the geometric excision comparison.

### Attempt 63/100 — Mayer--Vietoris

**Markdown proof.** The Mayer--Vietoris sequence for `A ∪ M` identifies
reduced `H₀(A ∩ M)` with a quotient of reduced `H₁(A ∪ M)`. Prove the union
has trivial `H₁`; connectedness follows.

**Lean.** No `H₁` vanishing or Mayer--Vietoris API for these subspaces exists.

**Revision.** `H₁(A ∪ M)=0` is a new sufficient hypothesis, not a theorem.

### Attempt 64/100 — Alexander duality

**Markdown proof.** Alexander duality translates disconnectedness of the
intersection into a nontrivial complement cohomology class. Compute the
complement from the connected basin and show the class vanishes.

**Lean.** The complement is not computed and the required compactification is
absent.

**Revision.** Use duality only after a parameter complement description.

### Attempt 65/100 — Vietoris--Begle

**Markdown proof.** A connected compact source with connected fibers maps
properly onto the target; Vietoris--Begle preserves reduced `H⁰`, so the
target is connected.

**Lean.** The source/map/fiber data are precisely the missing carving data.

**Revision.** The cohomological theorem is conditional and weaker as a
constructor than the existing connected-image theorem.

### Attempt 66/100 — shape equivalence

**Markdown proof.** The target has the shape of the connected frozen source
because both are neighborhoods of the same filled-Julia continuum. A
connected shape has trivial reduced `H⁰`, so the target is connected.

**Lean.** Shape equivalence is not established and trivial shape does not
force the literal compact set to be connected without additional hypotheses.

**Revision.** Prove a concrete cell-like map before invoking shape theory.

### Attempt 67/100 — persistent `H₀`

**Markdown proof.** The filtered groups `H₀(A(c,n) ∩ M)` cannot gain a new
class because the fixed Green function has no basin critical point.

**Lean.** Restriction to `M` creates boundary critical events not controlled
by the dynamical Laplacian.

**Revision.** Need a parameter filtration and a no-birth theorem.

### Attempt 68/100 — cohomological dimension

**Markdown proof.** The planar target has cohomological dimension one; a
disconnected compact set would have an extra degree-zero class forbidden by
the dimension spectral sequence.

**Lean.** Dimension bounds do not eliminate reduced `H⁰`; disconnected
zero-dimensional sets are planar.

**Revision.** Dimension theory cannot replace connectedness data.

### Attempt 69/100 — idempotent completion

**Markdown proof.** A nontrivial idempotent in the algebra of locally constant
functions on the target splits the category. Descent from the connected source
forbids the split.

**Lean.** Idempotent descent is not proven for the pullback; the finite-etale
probe is exactly the unresolved split.

**Revision.** Keep the idempotent as an obstruction certificate.

### Attempt 70/100 — universal coefficient argument

**Markdown proof.** Compute connectedness with every coefficient ring. Since
all degree-zero reduced homology groups vanish after tensoring, the integral
group vanishes.

**Lean.** The vanishing premise is not established over any coefficient
ring; coefficient changes do not create it.

**Revision.** Coefficients refine a proof after geometric vanishing is known.

## Batch H — non-Archimedean, tropical, and computational models

### Attempt 71/100 — Berkovich specialization

**Markdown proof.** A connected Berkovich affinoid models the parameter
intersection. Specialization to the complex plane has connected fibers, so
the image is connected.

**Lean.** No Berkovich space or complex specialization theorem exists.

**Revision.** This is a potential external realization model, not a proof.

### Attempt 72/100 — tropical tree

**Markdown proof.** Tropicalize the escape-rate function. The tropical
sublevel is a connected polyhedral tree; the complex intersection is its
analytic inverse image with connected fibers.

**Lean.** Tropicalization and connected analytic fibers are absent.

**Revision.** Need a faithful tropical-to-complex specialization theorem.

### Attempt 73/100 — Hubbard-tree skeleton

**Markdown proof.** Collapse each filled Julia set to a finite Hubbard tree
and identify parameters by equal tree data. The source interval maps onto
the intersection.

**Lean.** The quotient map and exact parameter fibers are not formalized.

**Revision.** Use as a conditional combinatorial realization.

### Attempt 74/100 — lamination tree

**Markdown proof.** The minor lamination quotient is a tree-like continuum.
A Green sector is an interval in the quotient and its inverse image is
connected by monotonicity.

**Lean.** No exact minor-lamination quotient onto the actual `M` is known
without the desired boundary theorem.

**Revision.** Model identification is the missing theorem.

### Attempt 75/100 — circle quotient

**Markdown proof.** Parameterize the boundary by angles, take the connected
angle interval for the Green level, and quotient by ray identifications.

**Lean.** Ray landing, angle interval identification, and quotient equality
are unavailable.

**Revision.** This is a graph-cut parapuzzle route, not the frozen model.

### Attempt 76/100 — arithmetic reduction

**Markdown proof.** Reduce quadratic parameters modulo primes and use
connectedness of reduction fibers to prove complex connectedness by lifting.

**Lean.** No arithmetic reduction-to-complex connectedness theorem exists;
reduction does not preserve the required topology.

**Revision.** Arithmetic models cannot replace analytic parameter control.

### Attempt 77/100 — interval arithmetic enclosure

**Markdown proof.** Compute certified polygonal inner and outer enclosures of
`M ∩ A(c,n)`. If every enclosure is connected and Hausdorff error tends to
zero, the limit is connected.

**Lean.** No certified enclosure algorithm or proof that all enclosures are
connected exists; numerical evidence is not a theorem for all `c,n`.

**Revision.** Use computation only for concrete instances.

### Attempt 78/100 — computable compactness

**Markdown proof.** If the target were disconnected, a computable rational
separation would be found by exhaustive orbit testing. The finite algorithm
would contradict the exact outer/inner approximation.

**Lean.** Noncomputability of the separation witness and lack of a uniform
finite escape bound prevent this algorithmic contradiction.

**Revision.** Compactness gives finite detection only after a stage
connectedness theorem.

### Attempt 79/100 — automated counter-separator search

**Markdown proof.** Encode a possible separator by polynomial inequalities and
prove the resulting real-algebraic system unsatisfiable for every depth.

**Lean.** There is no uniform quantifier-elimination proof and the separator
need not be semialgebraic.

**Revision.** Automation can test finite examples but cannot close the
unbounded frontier.

### Attempt 80/100 — certified cell adjacency

**Markdown proof.** Use a certified planar arrangement of finite orbit
boundaries. Show its adjacency graph is connected by a finite graph search,
then pass to the limit.

**Lean.** No arrangement construction or limit preservation is available,
and finite adjacency need not persist at the Mandelbrot boundary.

**Revision.** Add exact finite-stage topology and a uniform limit theorem.

## Batch I — Lean-level closure and logical audits

### Attempt 81/100 — remove the frontier declaration

**Markdown proof.** Delete the target axiom and compile the root. If all
imports still prove the theorem, the declaration was redundant.

**Lean.** Removing the declaration leaves the straddling theorem with an
unsolved goal. The root does not compile.

**Revision.** The declaration is still a genuine dependency.

### Attempt 82/100 — theorem dependency graph

**Markdown proof.** Search all imported declarations for a theorem whose
conclusion is the target or whose hypotheses are all proved. Follow the graph
to its leaf.

**Lean.** The graph terminates at
`green_sublevel_intersection_categorical` or at the conditional carving
theorem.

**Revision.** Preserve the explicit frontier and document the dependency.

### Attempt 83/100 — theorem search by connectedness

**Markdown proof.** Apply every `IsConnected` theorem in Mathlib to the
intersection, using connectedness of `A` and `M`.

**Lean.** The available image, union, and path theorems do not include
intersection of arbitrary connected sets.

**Revision.** Need a special geometric intersection theorem.

### Attempt 84/100 — rewrite through the categorical equivalence

**Markdown proof.** Rewrite the categorical target to the set target, apply
the direct Green-sublevel connectivity theorem, then rewrite back.

**Lean.** The equivalence theorem rewrites the statement but leaves the
intersection connectedness goal unchanged.

**Revision.** Equivalence is a bridge, not a proof.

### Attempt 85/100 — use `mandelbrot_set_connected`

**Markdown proof.** The intersection is a connected subspace of `M`, because
it contains `c` and is defined by an open neighborhood.

**Lean.** A subspace containing a point of a connected space need not be
connected; no `IsConnected` inheritance applies to arbitrary subsets.

**Revision.** Supply a connected-component or carving argument.

### Attempt 86/100 — use `green_sublevel_translate_connected`

**Markdown proof.** The intersection is a connected subspace of the
connected Green translate because it contains the translated critical point.

**Lean.** Again, arbitrary subsets of connected spaces need not be connected;
the straddling hypothesis gives no component equality.

**Revision.** Prove the intersection equals one connected component.

### Attempt 87/100 — invoke `IsPreconnected.inter`

**Markdown proof.** Both sets are preconnected; their intersection contains
`c`, so `IsPreconnected.inter` gives preconnectedness.

**Lean.** Mathlib's intersection lemmas require stronger hypotheses such as
one set being open/closed in a suitable connected space; the present
hypotheses do not meet them.

**Revision.** Establish a special relative-open/closed condition, which is
not known.

### Attempt 88/100 — prove openness of `M` in the Green piece

**Markdown proof.** The straddling intersection is relatively open in the
connected Green source, contains `c`, and its complement is relatively
closed; therefore it is a connected component.

**Lean.** `M` is not open in the parameter plane or in the Green source at
boundary points.

**Revision.** Boundary regularity would be a new MLC-level theorem.

### Attempt 89/100 — use the categorical root

**Markdown proof.** The categorical MLC root implies local connectedness of
`M`; local connectedness gives connected Green intersections.

**Lean.** The categorical root itself depends on the frontier axiom through
`CategoricalRoot.lean`; using it is circular and the axiom collector exposes
the cycle.

**Revision.** No circular use of the root is admissible.

### Attempt 90/100 — use the compatibility root

**Markdown proof.** The set-theoretic `MLC.mlc_conjecture` is equivalent to the
categorical root, so it proves the target.

**Lean.** The compatibility root also depends on
`green_sublevel_intersection_categorical`; this is direct circularity.

**Revision.** Keep the frontier below both roots in the dependency graph.

## Batch J — hybrid constructions and minimal reductions

### Attempt 91/100 — incidence space plus `K₀`

**Markdown proof.** The filled-Julia incidence space is connected after
discarding escaping fibers. Its projection has target `S`; finite-etale
probes pull back to constant probes on the incidence space.

**Lean.** Connectedness of the restricted incidence space and exact
projection image are both missing.

**Revision.** Prove incidence connectedness or use it as the future carving
source.

### Attempt 92/100 — Böttcher family plus outer stages

**Markdown proof.** The near-infinity Böttcher motion maps into every outer
orbit stage. Compatibility over `N` gives a surjection onto the outer limit,
which is `S`.

**Lean.** The motion is only local near infinity; no maps into all finite
stages or compatible limit surjection are constructed.

**Revision.** Extend the Böttcher family and prove finite-stage image
compatibility.

### Attempt 93/100 — puzzle motion plus two-sided envelope

**Markdown proof.** A graph-cut puzzle motion supplies connected finite
images, while the outer/inner envelope identifies their limit with `S`.

**Lean.** The current piece is not graph-cut, and no motion-image equality
with the outer/inner stages exists.

**Revision.** Introduce a separate genuine parapuzzle layer.

### Attempt 94/100 — proper map plus inverse limit

**Markdown proof.** At every stage a proper connected-source map covers the
finite intersection. Compatible maps give a proper surjection from the
inverse limit to `S`; connectedness follows.

**Lean.** Neither finite proper maps nor compatibility are available.

**Revision.** This is a precise sufficient structure for a future proof.

### Attempt 95/100 — harmonic source plus external rays

**Markdown proof.** Harmonic minimum principle gives a connected dynamical
source; external rays identify its boundary with the parameter boundary.
The combined map is a surjective carving.

**Lean.** The source theorem is proved, but the external-ray identification
is missing.

**Revision.** The missing boundary identification is the exact frontier.

### Attempt 96/100 — product of phase and parameter spaces

**Markdown proof.** Construct a connected product correspondence
`E ⊂ A(c,n) × K_c` whose two projections identify phase and parameter
coordinates. The parameter projection is `S`, so `S` is connected.

**Lean.** No relation with both exact projections is defined; a connected
product relation is not automatic from connected fibers.

**Revision.** Define and prove the correspondence as a carving datum.

### Attempt 97/100 — conservative realization

**Markdown proof.** Add only a continuous map from the connected source to
the target with exact image; no holomorphy or properness is needed. The image
theorem proves the frontier with minimal assumptions.

**Lean.** This is exactly `TopCatSurjectiveMorphism` and is already proved
conditionally.

**Revision.** The remaining work is existence, not connectedness transport.

### Attempt 98/100 — exact-image theorem as the smallest missing lemma

**Markdown proof.** Prove

```text
∃ f : A(c,n) → A(c,n) ∩ M,
  Continuous f ∧ f '' A(c,n) = A(c,n) ∩ M.
```

Connectedness of the source then gives the target.

**Lean.** `SpaceHolomorphicCarvingData` and
`DouadyHubbardYoccozCategoricalCarvingData` formalize this implication.
Existence of `f` is not derivable from the current base.

**Revision.** This is the minimal honest future theorem.

### Attempt 99/100 — conditional equivalence audit

**Markdown proof.** Show that the frontier is equivalent to universal
existence of the minimal exact-image map, not merely implied by it. One
direction is connected image; the other uses a constant map only when the
target is already known connected.

**Lean.** The implication from carving to the frontier is formalized. The
reverse implication would require selecting a continuous surjection from a
connected source onto every connected target, which is not available for
arbitrary subspaces without additional topology.

**Revision.** Carving is a sufficient strengthening, not literally equivalent
without a separate universal-source theorem.

### Attempt 100/100 — final axiom-surface audit

**Markdown proof.** Run the complete repository proof with the current target
axiom removed, then run the categorical and set-theoretic equivalence
bridges. If the target is derivable, `check_axioms.lean` will report no
frontier declaration.

**Lean.** `make check` still reports the target declaration. The only
axiom-clean path reaches the conditional theorem

```lean
DouadyHubbardYoccozCategoricalTheorem →
  GreenSublevelIntersectionCategoricalData
```

and stops at existence of the carving datum.

**Revision.** Stop after 100 attempts without changing the axiom surface.
The exact missing mathematical statement is now isolated rather than hidden
behind a new equivalent axiom.

## One-hundred-attempt conclusion

The attempts fall into three logically distinct classes:

1. **Invalid general topology/invariant claims.** Connectedness of the two
   factors, their hulls, their Reeb graphs, or their `K₀` ranks does not imply
   connectedness of their intersection.
2. **Valid conditional transports.** A continuous surjection, a connected
   finite-stage inverse system with exact image, probe restriction-surjectivity,
   or a genuine phase--parameter motion would prove the target. These are
   already represented by the current categorical bridge.
3. **Research-scale realization theorems.** Böttcher extension, external-ray
   landing, straightening families, Hubbard/lamination quotients, and
   quasiconformal surgery can potentially construct the missing data, but no
   such construction is currently formalized.

**AXIOM STATUS: NO AXIOM DISCHARGED.**

The checked root still uses exactly:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

No `sorry`, new axiom, circular root invocation, or unproved identification
of the frozen Green model with a classical Yoccoz parapuzzle was introduced.
