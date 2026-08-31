# TASK 59 — Isolate an axiom-free moving-window main route

## Context

The repository now has generic local-connectivity consumers:

```lean
ParameterPieceLcAtData
ConnectednessWindowParameterPieceData
lc_at_of_shrink_of_family_data
lc_at_of_connectednessWindow_family_data
```

Result 58 also added generic finite-side endpoint theorems in
`Mlc/InfinitelyRenormalizable.lean`.

However, the direct/main route still packages its finite branch through frozen
para-puzzle connectivity data. The live frontier axiom remains:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

## Goal

Create a conditional route that is ready to consume a genuine moving-window
provider once one exists, without claiming that provider has been constructed.

## Work

### Main strategy interface

Add a theorem, in `Mlc/MainConjecture.lean` or a focused adjacent module, with a
finite branch supplied by a generic moving-window contract. A suitable shape is:

```lean
∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
  (_h : FinitelyRenormalizable c),
  ∃ (W K : ℕ → Set ℂ),
    ConnectednessWindowParameterPieceData c W K
```

Use the existing generic finite-side endpoint to derive
`LocallyConnectedAt MandelbrotSet ⟨c, hc⟩`, then apply the existing strategy
theorem. Retain the current IR classification and molecule bridge inputs.

Do not require the provider to mention `ParaPuzzlePieceAt`.

### Direct route payload

Add a parallel structure in `Mlc/DirectRoute.lean`, for example:

```lean
structure DirectMovingWindowMLCData : Prop where
  finite_branch : ...
  ir_classification : IRClassificationData
  satellite_bridge : ...
```

and a theorem deriving `LocallyConnectedSpace mandelbrotSet` from it.

The new structure and theorem must be independent of:

- `ParaPuzzlePieceAt`;
- `ParaPuzzlePieceInterMandelbrotConnectedData`;
- `green_sublevel_translate_inter_mandelbrot_connected`;
- `PuzzleBoundaryMotionHyp`.

Preserve all old direct-route structures and theorem names.

### Satellite audit

Inspect `Mlc/MoleculeConjectureBridge.lean` only to classify its output:

- generic satellite LC output that can feed the new route;
- frozen principal-nest shrinkage/source dependencies that remain separate.

Do not rewrite the satellite shrinkage theorem in this task.

## Constraints

- No new axiom, `sorry`, or `admit`.
- Do not delete the frontier axiom.
- Do not fabricate a moving family by aliasing the old para-puzzle pieces.
- Do not continue Böttcher/parameter-ray work.
- Keep edits focused and compatible.
- Do not commit.

## Validation

Run:

```bash
lake build
lake env lean check_axioms.lean
```

## Report

Write:

`plan/GPT54_RESULT_59_ISOLATE_MOVING_WINDOW_MAIN_ROUTE.md`

State the exact provider contract and remaining frozen dependencies.
