# Categorical MLC plan

## Current state

- `MLC.Categorical.categorical_mlc_conjecture` is the canonical root
  formulation. It states local connectedness of the Mandelbrot object
  `TopCat.of MLC.mandelbrotSet`.
- `MLC.mlc_conjecture` is a compatibility theorem, and
  `MLC.Categorical.mlc_conjecture_iff_categorical` proves equivalence with the
  categorical statement.
- The categorical and set-theoretic parameter-frontier inputs are equivalent
  through `greenSublevelIntersectionCategoricalData_iff`.
- The categorical residual product input is equivalent to the original
  conjunction through `categoricalResidualOpenVirtualNearMoleculeData_iff`.
- `check_axioms.lean` checks both root formulations and requires the same
  project-level axioms:
  `MLC.green_sublevel_intersection_categorical` and
  `MLC.residualOpenVirtualNearMoleculeAxiom`.

## Categorical frontier

1. `GreenSublevelIntersectionCategoricalData` is now known to be exactly the
   old set-theoretic straddling statement, via
   `greenSublevelIntersectionCategoricalData_iff`. The base closure proves
   connectedness of the Green-sublevel approximation and identifies the image
   of its pullback with the set intersection, but does not prove that the
   pullback is connected.
2. The missing categorical theorem is now formalized as
   `DouadyHubbardYoccozCategoricalTheorem`: for every straddling piece,
   construct a surjective morphism in `TopCat` from the connected translated
   Green sublevel to the Green-sublevel/Mandelbrot pullback. The theorem
   `greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz` proves
   the connected-image consequence. A constructor from
   `SpaceHolomorphicCarvingData` shows that a genuine space-holomorphic
   parameter carving supplies this categorical datum. The existence of that
   morphism is still the Douady--Hubbard/Yoccoz parameter--dynamical
   correspondence; category theory transports connectedness but does not
   manufacture the morphism.
3. Prove the residual categorical input by discharging its two product
   components: the pseudo-Siegel a priori bounds and the virtual
   near-Molecule interpolation problem. The product/limit wrapper is already
   formalized and adds no mathematical strength.
4. Refine the categorical parameter-puzzle limit so its image and connectedness
   properties are stated through categorical cones and morphisms, with the
   existing set lemmas used only as proved equivalence bridges.

## Model correction: full Green sublevels versus Yoccoz parapuzzles

The current source

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
```

is the translate of the **entire** dynamical Green sublevel. It is connected
for `c ∈ MandelbrotSet`, but it is not the classical graph-cut Yoccoz puzzle
piece. The new theorem

```lean
iInter_green_sublevel_translate_eq_translate_filledJulia
```

proves

```text
⋂ n, {c' | G_c(c' - c) < 2^(-n)} = (fun z => z + c) '' K c.
```

Thus this tower generally retains a translated filled Julia set and does not
shrink to the center parameter. The remaining straddling axiom is consequently
not a direct formalization of the usual finite-level Yoccoz parapuzzle theorem.
The sound next choices are:

1. prove the current full-sublevel intersection theorem directly from a new
   phase--parameter realization result; or
2. introduce genuine graph-cut dynamical and parameter parapuzzles, prove their
   carving/properness theorem, and use those pieces for the local-connectivity
   root.

The existing `DouadyHubbardYoccozCategoricalCarvingData` is still a valid
conditional connected-image interface, but its exact-image field remains an
explicit research obligation and must not be attributed to Yoccoz without the
additional graph, motion, and phase--parameter hypotheses.

## Ten-iteration frontier proof search

The detailed proof attempts are recorded in
`refs/green_sublevel_intersection_categorical_proof_attempts.md`. Ten routes
were tried and revised:

1. connectedness of the two factors;
2. compact decreasing outer stages;
3. increasing inner uniform-bound stages;
4. finite detection of a separation by compactness;
5. Green-function monotonicity;
6. Böttcher/external-ray parametrization;
7. classical Yoccoz parapuzzles;
8. finite-etale `K₀` component detection;
9. a regular epimorphism in `TopCat`;
10. a two-sided outer/inner realization comparison.

The exact formalized successes are the orbit-envelope limit identities and
compactness in `Mlc/CategoricalMandelbrot.lean`, the `K₀`-shadow equivalence
and excision reformulations in `Mlc/EfimovCategoricalBridge.lean`, and the
surjective connected-image implication for categorical carving. The remaining
existence/image equality is the same phase--parameter theorem in every
presentation; no proof attempt reduced the checked axiom surface.

## Second ten-iteration proof round

The second round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round2.md`.
It tried continuum separation, proper polynomial-like pullbacks, straightening
families, external-ray graph cuts, harmonic measure, renormalization inverse
limits, prime ends, Alexander duality, finite-stage regular epimorphisms, and a
minimal continuous-surjection formulation. The last route is the exact
formalized reduction already represented by
`TopCatSurjectiveMorphism`.

The CLI axiom check remains intentionally unchanged:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.green_sublevel_intersection_categorical
```

The main next step is still to construct the exact-image parameter carving
map, or an equivalent compatible outer/inner realization, without adding that
existence statement as a replacement axiom.

## Third ten-iteration proof round

The third round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round3.md`.
It tested ten different mechanisms: frozen-basis/local-connectedness limits,
pure planar full-continuum intersection, finite-time outer orbit stages,
escape-coordinate polynomial lemniscates, quasiconformal wringing,
Teichmuller space, `K_0` probe extension, strong Mittag--Leffler inverse
limits, Green-gradient deformation, and analytic continuation of separating
probes.

The formalization checks confirm that the available finite-stage limit
theorems require connected stage intersections that are not established, while
the quasiconformal, Teichmuller, and probe-continuation routes require the same
exact parameter realization already exposed by
`TopCatSurjectiveMorphism`. The frontier is therefore unchanged and the
axiom-minimal target remains the connected-source carving map.

## Fourth ten-iteration proof round

The fourth round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round4.md`.
It tested parameter Green-potential level sets, finite kneading graphs,
branched-covering arguments, hyperbolic-component unions, filled-Julia
semicontinuity, lamination quotients, shape theory, Mayer--Vietoris
`K`-theory, induction on Green depth, and first-exit path arguments.

The round found no axiom-free discharge. Finite-stage methods still require
connected finite-stage intersections; potential, shape, and homological
methods require new parameter-plane information; and the dynamical
functional equation does not preserve Mandelbrot membership under translation.
The exact carving/realization map remains the smallest sufficient missing
input.

**Axiom status: no axiom discharged.** The checked surface remains the three
Lean foundations plus
`MLC.residualOpenVirtualNearMoleculeAxiom` and
`MLC.green_sublevel_intersection_categorical`.

## Fifth ten-iteration proof round

The fifth round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round5.md`.
It tested effective quotients/coequalizers, Stein factorization, monotone
decompositions, pinched-disk models, polynomial-like moduli, covering-space
lifts, categorical effective descent, Vietoris--Begle degree-zero invariants,
renormalization coequalizers, and an exact dependency audit of the Lean root.

All categorical and invariant-level routes still require an exact continuous
image map from a connected source to the literal straddling intersection.
The existing `TopCatSurjectiveMorphism` theorem proves the transport once that
map is supplied, but no current theorem constructs it.

**Axiom status: no axiom discharged.** The checked surface is unchanged.

## Sixth ten-iteration proof round

The sixth round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round6.md`.
It tested polynomial-hull arguments, Riemann-map/equipotential crosscuts,
winding-number and topological-degree obstructions, Loewner evolution,
equipotential trees, Berkovich specialization, categorical `pi_0` base
change, Runge extension of component probes, and an explicit test of replacing
the frontier by its conditional carving theorem.

These routes again stop at an exact parameter-side map, connected-fiber
specialization, or an equivalent theorem. The current categorical bridge
already proves the connected-image implication and the axiom collector
confirms that the existence part is still absent.

**Axiom status: no axiom discharged.** The checked surface is unchanged.

## Seventh ten-iteration proof round

The seventh round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round7.md`.
It tested the universal filled-Julia incidence space, Hubbard-tree/regulated
arc arguments, modulus bounds for separating annuli, semialgebraic orbit
stages, monodromy, structural-stability strata, external-ray incidence,
categorical `K_0` localization, universal polynomial-like families, and a
formal dependency audit.

The incidence, tree, modulus, and family routes all require a new exact
parameter realization or finite-stage connectivity theorem. The existing
`TopCatSurjectiveMorphism` and finite-etale interfaces formalize the
connectedness transport once such data are supplied, but do not construct
them.

**Axiom status: no axiom discharged.** The checked surface is unchanged.

## Eighth ten-iteration proof round

The eighth round is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_round8.md`.
It tested good-cover nerves, component cosheaves, persistence and Reeb
graphs, Thurston pullback contraction, extension of the near-infinity
Böttcher family, stable-component gluing, locale/frame descent,
noncommutative `K_0`, and finite obstruction extraction.

The most concrete remaining implementation route is to extend the sound
near-infinity Böttcher family to a basin-wide, jointly holomorphic family and
then prove its exact image is the literal straddling intersection. The
alternative gluing and invariant routes still require connected finite stages
or effective descent hypotheses.

**Axiom status: no axiom discharged.** The checked surface is unchanged.

## Up-to-100 proof search

The one-hundred-attempt report is documented in
`refs/green_sublevel_intersection_categorical_proof_attempts_100.md`.
The attempts are grouped into ten batches covering planar continuum theory,
potential/PDE methods, complex dynamics and renormalization, quasiconformal
and Böttcher realization, finite orbit approximations, categorical descent,
homology/shape/`K_0`, non-Archimedean and computational models, Lean-level
audits, and hybrid exact-image constructions.

The search stopped at attempt 100 without a discharge. It confirms the same
minimal frontier: construct an exact continuous (preferably
space-holomorphic) image map from the connected frozen Green source onto the
literal straddling intersection, or prove an equivalent connected-stage and
probe-descent theorem.

**Axiom status: no axiom discharged.** The checked surface is unchanged.

## Two-sided orbit approximation of the Mandelbrot object

`Mlc/CategoricalMandelbrot.lean` now contains a separate two-sided envelope:

```lean
innerOrbitSet N :=
  {c | ∀ n, ‖orbit c 0 n‖ ≤ (N : ℝ)}

outerOrbitSet N :=
  {c | ‖c‖ ≤ 2 ∧ ∀ n ≤ N, ‖orbit c 0 n‖ ≤ 2}
```

The inner system is increasing and exhausts `M`:

```lean
⋃ N, innerOrbitSet N = MandelbrotSet
```

because every bounded orbit has a real bound and hence a natural bound above
it. The outer system is decreasing, each stage is compact, and

```lean
⋂ N, outerOrbitSet N = MandelbrotSet
```

by the Molecule repository's `Molecule.mandelbrot_eq_inter` characterization
and its universal parameter-disk bound. The corresponding categorical
approximations are connected to the Mandelbrot object by explicit finite-stage
morphisms:

```text
innerOrbitApproximation N  --->  setApproximation
setApproximation              --->  outerOrbitApproximation N
```

This is not a rewrapping of the existing Green/puzzle API. It separates
finite-time nonescape observations from uniform bounded-orbit witnesses and
gives two independent limit presentations of `M`. It is the intended base for
a later outer/inner realization comparison: a proposed categorical or
phase--parameter construction must map into the outer stages and eventually
land in an inner stage, rather than choosing `M` itself as a vacuous source.

The generic transfer lemmas
`TwoSidedSetApproximation.isConnected_of_inner` and
`TwoSidedSetApproximation.isPreconnected_of_outer` make the future obligations
explicit. To obtain connectedness from the inner side, it is enough to prove
connectedness of every increasing uniform-bound stage and exhibit their common
base point. To obtain preconnectedness from the outer side, it is enough to
prove preconnectedness of every compact finite-prefix enclosure; the decreasing
compact-intersection theorem then applies. Neither condition is currently
claimed for the actual stages, so no new project axiom has been introduced.

## Efimov/Pacman assessment

The TeX sources for Efimov's five relevant papers are stored in
`refs/`; the detailed audit is in
`refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md`.
Their usable inputs are:

- continuous `K`-theory as a localizing invariant on dualizable presentable
  stable categories;
- rigidity, nuclearity, trace-class maps, and internal-Hom descriptions for
  localizing motives;
- inverse-limit formulas for continuous localizing invariants under strong
  Mittag--Leffler hypotheses;
- theorem-of-the-heart and `KH`/Quillen dévissage for dualizable categories
  with suitable `t`-structures.

None of these results constructs the Pacman refinement tower or a realization
to `TopCat / ℂ`. In particular, they do not imply connectedness of
`{c' | green_function c (c' - c) < 2^(-n)} ∩ MandelbrotSet`. A genuine
space-holomorphic carving/motion statement remains the exact missing
phase--parameter bridge. The new Lean layer therefore exposes only explicit
conditional interfaces and a degreewise `K_n` shadow; it does not claim that
these interfaces are instantiated by Efimov's theorems.

The first honest version of that interface is now in
`Mlc/EfimovCategoricalBridge.lean`:

1. `DualizablePacmanTower` stores rigid monoidal levels, refinement functors,
   and explicit adjacent adjunctions.
2. `StrongMittagLefflerData` records Efimov's eventual essential-constancy
   clause and the `Φₙₖ` functors with both adjoint witnesses, including the
   colimit-preservation field corresponding to strong continuity. The fields
   are explicit inputs; no stable-infinity-category theorem is claimed.
3. `PacmanKTheory` exposes a graded additive finite-level invariant, while
   `KTheoryMittagLeffler` applies Mathlib's native type-valued
   `Functor.IsMittagLeffler` degree by degree. This is a checkable shadow, not
   an implementation of actual algebraic or continuous `K`-theory.
   `KTheoryLimitComparison` packages the separate continuous-limit comparison
   input rather than pretending that Mathlib proves Efimov's theorem.
4. `PacmanRealization` records a compatible realization into
   `Over (TopCat.of ℂ)`.
5. `SpaceHolomorphicCarvingData` contains the non-opaque bridge still needed
   for the frontier: the already-proved translated Green sublevel as the
   fixed connected source, a space-holomorphic map, and an exact image
   equality with the Green-sublevel/Mandelbrot intersection. This prevents
   the interface from choosing the target itself as a vacuous source.

`greenSublevelIntersectionCategorical_of_efimovBridge` proves the final
connectedness implication from that carving data. The categorical/K-theory
interfaces do not themselves discharge the carving field or the residual
near-Molecule axiom; those remain the two checked project-level inputs.

## Later categorical/K-theory work

The interface is now present, but its mathematical instantiation remains later
work: construct the actual stable/dualizable Pacman levels, identify the
graded invariant with genuine `K_n` for `n ≥ 2`, prove the Efimov
limit-comparison input, and establish the space-holomorphic carving image.

## Ten-iteration frontier search

The requested breadth search was completed without introducing a disguised
replacement axiom:

| Iteration | Route | Result |
| --- | --- | --- |
| 1 | Checked branch, imports, and axiom closure | The categorical root still has exactly the two project-level frontier axioms. |
| 2 | Historical Böttcher-motion/Słodkowski scaffolding | The historical motion files are not on this branch and their key fields are assumptions, so importing them would not discharge the frontier. |
| 3 | Generic topological intersection arguments | Connectedness of the Green translate and of `MandelbrotSet` separately is insufficient; connected intersections need a carving or monotonicity theorem. |
| 4 | Historical Böttcher and boundary-motion search | The available scaffolding does not construct a nontrivial parameter motion or identify its image with the target intersection. |
| 5 | Yoccoz and Molecule dependency search | Neither dependency supplies the required parameter--dynamical correspondence for the current Green/Mandelbrot pullback. |
| 6 | Categorical limits and compact nested intersections | `isPreconnected_iInter_of_sequence` proves a decreasing intersection of compact preconnected sets is preconnected, but the current target is an open Green sublevel intersected with `M`; no qualifying compact connected approximants are available. `TopCat` limits alone preserve only the universal property, not connectedness. |
| 7 | Exact Efimov hypotheses | The inverse-limit $K$-theory results require dualizable stable categories, strong Mittag--Leffler transition data, and realization hypotheses. The current `RenormalizationTower` contains only `BMol` objects and nonempty renormalization relations. |
| 8 | Conditional motive-to-parameter realization | Implemented the honest conditional interface in `Mlc/EfimovCategoricalBridge.lean`: categorical tower, graded invariant, realization, and fixed-source carving fields remain explicit inputs; no frontier theorem is asserted from packaging alone. |
| 9 | Molecule special strata and proper-map reductions | `Molecule.MolSet` is only `closure MainCardioid`; its connectedness and compactness do not identify it with `MandelbrotSet` or contain the target intersection. The dependency's proper-map lemmas apply to power-map preimages, not to this parameter pullback. |
| 10 | Consolidation and reference audit | The smallest non-circular next theorem is a genuine Douady--Hubbard/Yoccoz carving or equivalent space-holomorphic motion whose image is the straddling intersection. Stale references to a nonexistent carving module were removed from the plan and motive bridge. |

The search therefore sharpened the target but did not discharge
`MLC.green_sublevel_intersection_categorical`. Efimov's results remain useful
for organizing a future $K_n$ tower, not for proving connectedness in the
parameter plane.

## 2026-09-04 Efimov breadth/depth search

The Google Scholar profile and the arXiv author feed were rechecked before
downloading the missing source archives. The repository now stores the
current relevant versions:

- `2405.12169v3`, *K-theory and localizing invariants of large categories*;
- `2502.04123v2`, *Localizing invariants of inverse limits*;
- `2505.13260v2`, *Some remarks on Quillen's Dévissage theorem*;
- `2510.17010v1`, *Rigidity of the category of localizing motives*;
- `2603.08653v2`, *Theorem of the heart for Weibel's homotopy K-theory*.

The source-level terminology scan found zero occurrences of `Mandelbrot`,
`Julia`, `Green`, `renormalization`, `holomorphic motion`, `connectedness`,
`local connectivity`, `Douady`, `Yoccoz`, `dynamical`, or `parameter plane`
in those five Efimov source trees. The source archives and API metadata are
integrity-checked and the extracted TeX is retained under `refs/`.

The deeper proof search gives a strict separation of obligations. Efimov's
theorems can justify the categorical portion:

1. build actual dualizable stable Pacman levels and strongly continuous
   transitions;
2. verify the strong Mittag--Leffler and homological-epimorphism hypotheses;
3. identify the resulting continuous `K`-theory limit, using `KH`/dévissage
   only after a valid `t`-structure is supplied.

They do not provide the independent geometric portion:

1. a conservative realization into `Over (TopCat.of ℂ)`;
2. equality of its image with the Green-sublevel/Mandelbrot pullback;
3. a connected-source space-holomorphic carving map.

Consequently the new source evidence strengthens the categorical interface
but does not discharge the checked frontier axiom. A PDF compilation probe
was also run; both new arXiv sources stop at the same missing local
`mathabx.sty` package in the available TeX installation, while gzip/archive
integrity and theorem/source scans succeed.

## 2026-09-05 finite-etale `K₀` component route

The next Efimov-inspired iteration replaces an unavailable exact continuous
`K`-theory implementation by the smallest finite-etale shadow that can still
see connectedness:

```lean
abbrev FiniteEtaleKZeroProbe (S : Set ℂ) := LocallyConstant S Bool
```

For every nonempty set `S`, the checked theorem
`isConnected_iff_finiteEtaleKZeroProbeTrivial` proves

```text
IsConnected S ↔ every locally constant Bool-valued probe on S is constant.
```

The proof is entirely axiom-free and forwards to Mathlib's
`isPreconnected_of_forall_constant`, `LocallyConstant.apply_eq_of_preconnectedSpace`,
and the restricted-continuity API. Thus the probe is not presented as genuine
algebraic `K₀`; it is the finite-etale/component-level part of a possible
degree-zero localizing invariant.

Two conditional Efimov interfaces are now available:

1. `FiniteEtaleKZeroDescentData` asks that every probe descend to one connected
   finite stage of an inverse system. Its `isConnected_of_finiteEtaleKZeroDescent`
   theorem is the topological analogue of strong Mittag--Leffler descent.
2. `FiniteEtaleKZeroRestrictionSurjective` asks for surjectivity of restriction
   from the connected translated Green sublevel to its Mandelbrot intersection.
   The theorem
   `finiteEtaleKZeroRestrictionSurjective_iff_isConnected` shows that, with
   the already-proved nonemptiness and ambient connectedness, this is exactly
   equivalent to the target connectedness statement. Consequently
   `greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroExcisionData`
   is a faithful relative-excision reformulation, not a weaker proxy or a new
   opaque axiom.

The generic categorical criterion
`imageConnected_intersection_of_finiteEtaleKZeroPullbackExcision` derives
connectedness of a pullback in `TopCat / ℂ` from source connectedness,
nonemptiness, and relative probe-surjectivity. Its target-specialized form is
the exact equivalence
`greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroPullbackData`.
`EfimovGreenSublevelKZeroBridge` now packages this pullback-excision input
alongside the rigid tower, strong-Mittag--Leffler data, graded invariant,
limit comparison, and realization. The bridge theorem derives the
categorical frontier from the pullback-excision field, but no field is
inferred from Efimov's papers: the missing geometric realization/excision
input remains the Douady--Hubbard/Yoccoz parameter--dynamical theorem. The
checked root axiom set is unchanged.

This does not constitute an unconditional discharge: because the pullback
excision statement is equivalent to the original categorical frontier, an
instance cannot be manufactured from the abstract Efimov tower fields alone.
The remaining proof obligation is now isolated as a concrete conservative
realization/excision theorem rather than an opaque connectedness declaration.

## 2026-09-05 categorical Douady--Hubbard/Yoccoz reformulation

The parameter--dynamical input is now stated in native categorical terms
without claiming an unproved instance:

- `TopCatSurjectiveMorphism S T` packages a continuous morphism
  `TopCat.of S ⟶ TopCat.of T` together with surjectivity of its underlying
  map.
- `isConnected_of_topCatSurjectiveMorphism` proves that a surjective
  `TopCat` morphism carries connected source subsets to connected target
  subsets, using Mathlib's `ConnectedSpace` and `IsConnected.image` APIs.
- `DouadyHubbardYoccozCategoricalCarvingData c n` specializes this to a
  morphism from the translated Green sublevel to its Mandelbrot pullback.
- `DouadyHubbardYoccozCategoricalTheorem` quantifies this carving datum over
  all straddling parameters. Its connected-image theorem
  `greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz` derives
  the current categorical frontier.
- `SpaceHolomorphicCarvingData.toDouadyHubbardYoccozCategoricalCarvingData`
  proves that the existing holomorphic carving interface implies the
  categorical one, including continuity and surjectivity of the induced
  `TopCat` morphism.

The remaining unproved statement is precisely the existence field in
`DouadyHubbardYoccozCategoricalTheorem`; it is not derivable from Efimov's
strong-Mittag--Leffler or `K`-theory interfaces alone. The root axiom set is
therefore unchanged and the new categorical theorem is a sound, strictly
structured reduction of the analytic frontier.

## Validation

Run:

```bash
make build
make check
./scripts/verify_output.sh
```
