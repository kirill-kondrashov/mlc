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
2. The missing categorical theorem is a genuine carving result: construct a
   connected parameter approximation and a morphism into the pullback whose
   ambient image is the full straddling intersection. In dynamical terms this
   is the Douady--Hubbard parameter--dynamical correspondence, or an
   equivalent space-holomorphic motion of the puzzle boundary. Category
   theory can transport connectedness once this morphism is constructed; it
   cannot provide the morphism from the current base axioms.
3. Prove the residual categorical input by discharging its two product
   components: the pseudo-Siegel a priori bounds and the virtual
   near-Molecule interpolation problem. The product/limit wrapper is already
   formalized and adds no mathematical strength.
4. Refine the categorical parameter-puzzle limit so its image and connectedness
   properties are stated through categorical cones and morphisms, with the
   existing set lemmas used only as proved equivalence bridges.

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

## Validation

Run:

```bash
make build
make check
./scripts/verify_output.sh
```
