# PLAN 04: Prove `MLC.green_sublevel_translate_inter_mandelbrot_connected`

**Status:** ACTIVE  
**Depends on:** `PLAN_00_frontier_overview.md`

## Goal

Replace the axiom

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected
```

by a theorem.

## Mathematical content

For `c ∈ MandelbrotSet` and `n : ℕ`, prove connectedness of

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet.
```

This is the parameter-space connectivity statement currently consumed by `Mlc/ParaPuzzleConnectivity.lean` after the dynamical Green-sublevel identification has been theoremized.

## Current formal state

The surrounding bridge infrastructure is present, but the currently visible route is still circular with respect to the remaining frontier.

More precisely:

- `Mlc/ParaPuzzleConnectivity.lean` proves the desired para-puzzle connectedness statement from two inputs, one of which is exactly the current target axiom `green_sublevel_translate_inter_mandelbrot_connected`.
- The alternative containment bridge in `Mlc/ParaPuzzleContainment.lean` proves `K c ⊆ DynamicalPuzzlePiece c n 0`, but its proof uses
  ```lean
  filled_julia_set_connected hc
  ```
  so it cannot currently be used to bypass PLAN 01.
- `Mlc/Quadratic/Complex/PuzzleBoundaryMotion.lean` already packages several transport targets, but they are data-conversion layers; they do not themselves prove the required connectedness theorem.

Therefore PLAN 04 is not yet independently executable as a theoremization step from the currently surfaced non-circular infrastructure.

## Readiness assessment

PLAN 04 is presently **not ready** for a clean frontier reduction.

- The formal architecture is well isolated.
- The remaining mathematical content is precise.
- But every visible proof route still depends either directly on the target axiom or indirectly on the unresolved `filled_julia_set_connected` frontier item.

## Likely proof ingredients

1. holomorphic motion / lambda-lemma transport of puzzle boundaries;
2. identification of para-puzzle pieces with Green-sublevel translates;
3. connectedness of the resulting parameter puzzle piece intersection with `M`.

## Success criterion

1. `Mlc/ParaPuzzleConnectivity.lean` uses a theorem instead of this axiom;
2. `make check` removes `MLC.green_sublevel_translate_inter_mandelbrot_connected`;
3. no weaker replacement axiom is introduced.
