# TASK 73 — Repair the finite boundary graph foundation

## Context

Result 72 identified a concrete, limited Lean foundation:

- continuous injective arcs on `Icc (0 : ℝ) 1`;
- finite union carrier;
- selected complementary component;
- refinement/nesting.

The attempted implementation stopped on API details, not on the mathematical
goal.

## Required repairs

### Arc compactness

Prove that each arc image is compact and closed from continuity on compact
`Icc`. Handle subtype/range normalization explicitly.

### Finite carrier

Use explicit finite induction or the correct `Finset` union theorem to prove
the carrier is closed.

### Open components in `ℂ`

Find and use an existing `LocallyConnectedSpace ℂ` result, or prove the
smallest local connectedness theorem needed from the metric/normed-vector-space
structure. Do not introduce an axiom or a target-shaped field.

### Refinement monotonicity

Prove selected-component inclusion under carrier inclusion and shared
basepoint complement membership. Isolate any intermediate subset proof required
by `connectedComponentIn`.

## Non-goals

- no Jordan curve/separation theorem;
- no bounded-component claim;
- no external rays/equipotentials;
- no Mandelbrot or phase–parameter theorem;
- no provider or root migration.

## Constraints

- no frontier axiom;
- no `ParaPuzzlePieceAt` alias;
- no new axiom, `sorry`, or `admit`;
- preserve APIs;
- do not commit.

## Verification

Run:

```bash
lake env lean Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean
lake build
lake env lean check_axioms.lean
```

## Result

Write:

`plan/GPT54_RESULT_73_REPAIR_FINITE_BOUNDARY_GRAPH_FOUNDATION.md`

If an API theorem is genuinely absent, report the exact missing Mathlib result
instead of hiding it in an opaque assumption.
