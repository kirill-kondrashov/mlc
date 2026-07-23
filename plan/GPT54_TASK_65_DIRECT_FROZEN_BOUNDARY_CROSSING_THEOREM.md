# TASK 65 — Prove the frozen boundary-crossing theorem

## Objective

Prove the exact specialized no-separation/boundary-crossing property isolated
by Stage 2, sufficient for:

```lean
IsConnected
  ({c' | green_function c (c' - c) < (1 / 2 : ℝ)^n} ∩ MandelbrotSet)
```

under the straddling hypothesis.

## Requirements

Use only genuine results about:

- `green_function c`;
- translated Green sublevels;
- `MandelbrotSet`;
- their boundaries, components, and continuum properties.

The conclusion must apply to the frozen translate exactly as stated. Do not
substitute a moving parapuzzle or a renamed `ParaPuzzlePieceAt`.

If a substantive classical boundary theorem is required but absent, document:

- its exact mathematical statement;
- why existing repository lemmas do not imply it;
- whether it is known for the frozen formulation or only for moving
  parapuzzles.

Do not add the missing theorem as an axiom or opaque hypothesis.

## Constraints

- no frontier axiom;
- no equivalent para-puzzle connectivity wrapper;
- no `sorry`, `admit`, or speculative shortcut;
- preserve all existing APIs;
- do not commit.

Write:

`plan/GPT54_RESULT_65_DIRECT_FROZEN_BOUNDARY_CROSSING_THEOREM.md`
