# TASK 70 — Instantiate the genuine quadratic parapuzzle provider

## Objective

Apply the abstract results to quadratic parameter space using actual finite
ray/equipotential/graph or equivalent moving-boundary data.

## Required provider fields

For every finitely renormalizable `c ∈ MandelbrotSet`, produce windows with:

- openness;
- basepoint membership;
- neighborhood basis/shrinkage;
- connectedness of `W n ∩ MandelbrotSet`;
- genuine phase–parameter meaning.

Then construct:

```lean
FiniteMovingWindowProviderData
```

without using the frozen axiom.

## Hard stop

If ray landing, graph construction, or phase–parameter correspondence is not
formalized, make no speculative edits. Name the first missing theorem and stop.

## Constraints

- no frozen `ParaPuzzlePieceAt` provider;
- no frontier axiom;
- no placeholders;
- no new axiom, `sorry`, or `admit`;
- do not reroute the root yet;
- do not commit.

## Result

Write:

`plan/GPT54_RESULT_70_QUADRATIC_PARAPUZZLE_INSTANTIATION.md`
