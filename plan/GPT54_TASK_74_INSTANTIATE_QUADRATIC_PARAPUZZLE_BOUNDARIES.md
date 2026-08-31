# TASK 74 — Instantiate quadratic parapuzzle boundary arcs

## Context

Result 73 completed the reusable finite graph module:

```lean
BoundaryArc
FiniteEmbeddedBoundaryGraph
FiniteEmbeddedBoundaryGraphFamily
```

The next source-side question is whether actual quadratic ray/equipotential
objects can populate this model.

## Audit and implementation

Search existing project modules for proved:

- external or parameter ray maps;
- rational-angle labels and finite combinatorics;
- equipotential/Green-level curves;
- landing endpoints;
- graph incidence and no-crossing;
- refinement/nesting;
- near-infinity ray parametrizations.

If such an object is genuinely proved, construct `BoundaryArc` data and prove
the required continuity/injectivity and endpoint facts. Add only the smallest
quadratic boundary constructor.

If the repository has only shells or axioms, do not wrap them as genuine arcs.
Report the first missing theorem, especially whether it is:

- a full external Böttcher coordinate;
- a ray landing theorem;
- a parameter-ray/equipotential construction;
- a phase–parameter correspondence.

## Constraints

- no frontier axiom;
- no frozen para-puzzle alias;
- no placeholder motion;
- no new axiom, `sorry`, or `admit`;
- no Mandelbrot connectedness claim yet;
- do not commit.

## Verification

Run targeted checks and, if editing source:

```bash
lake build
lake env lean check_axioms.lean
```

## Result

Write:

`plan/GPT54_RESULT_74_INSTANTIATE_QUADRATIC_PARAPUZZLE_BOUNDARIES.md`
