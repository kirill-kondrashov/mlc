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

The TeX sources for Efimov's three relevant papers are stored in
`refs/`; the detailed audit is in
`refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md`.
Their usable inputs are:

- rigidity, nuclearity, trace-class maps, and internal-Hom descriptions for
  localizing motives;
- inverse-limit formulas for continuous localizing invariants under strong
  Mittag--Leffler hypotheses;
- theorem-of-the-heart and `KH` dévissage for dualizable categories with
  suitable `t`-structures.

None of these results constructs the Pacman refinement tower or a realization
to `TopCat / ℂ`. In particular, they do not imply connectedness of
`{c' | green_function c (c' - c) < 2^(-n)} ∩ MandelbrotSet`. The current
carving target `ParaPieceCarvedByMotion` remains the exact missing
phase--parameter bridge. Adding a `K_n` statement before that bridge would
only add an unconnected abstraction, so no Lean K-theory placeholder is
introduced.

The next sound categorical interface is therefore conditional and should
contain:

1. a strongly Mittag--Leffler sequence of Pacman models;
2. its stable/dualizable categorical realization;
3. an equality between its realized parameter locus and the Green-sublevel
   pullback;
4. a space-holomorphic carving map, which can then be consumed by
   `ParaPuzzleCarvingReduction`.

## Later categorical/K-theory layer

After the categorical frontier is stable, introduce the category and functors
needed for the nested boundary/interior approximations. Define the relevant
universal constructions first; add a $K_n$ interface for $n \ge 2$ only after
those constructions have concrete objects, morphisms, and comparison maps.

## Validation

Run:

```bash
make build
make check
./scripts/verify_output.sh
```
