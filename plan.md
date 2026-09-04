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

1. Prove `GreenSublevelIntersectionCategoricalData` directly. Work with
   approximations in `Over (TopCat.of ℂ)`, pullback intersections, and the
   universal parameter-puzzle tower rather than first proving the old
   set-theoretic connectivity statement.
2. Prove the residual categorical input by discharging its two product
   components: the pseudo-Siegel a priori bounds and the virtual
   near-Molecule interpolation problem. The product/limit wrapper is already
   formalized and adds no mathematical strength.
3. Refine the categorical parameter-puzzle limit so its image and connectedness
   properties are stated through categorical cones and morphisms, with the
   existing set lemmas used only as proved equivalence bridges.

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
