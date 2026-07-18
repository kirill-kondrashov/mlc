# TASK 58 — Migrate finite-side consumers to the moving-window interface

## Objective

Continue removing representational coupling to the frozen
`ParaPuzzlePieceAt`/transport-data route while preserving the current frontier.

The current axiom remains:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

Result 57 added a compiling adapter in `Mlc/LcAtOfShrink.lean`, but it still
wraps the old frozen transport provider. This task migrates downstream
theorem-facing consumers only.

## Required work

### 1. Generic finite-side theorem

In `Mlc/InfinitelyRenormalizable.lean`, add a theorem accepting a genuine
generic moving-window package, preferably:

```lean
ConnectednessWindowParameterPieceData c W K
```

or the minimal:

```lean
ParameterPieceLcAtData c P
```

Use the existing generic local-connectivity consumer. Keep
`FinitelyRenormalizable c` and existing shrinkage hypotheses only if needed by
the theorem statement; do not pretend those hypotheses construct the windows.

### 2. Compatibility wrappers

Route existing theorems such as:

```lean
mlc_finitely_renormalizable_of_paraPuzzleConnectedData
mlc_finitely_renormalizable_of_paraPuzzleTransportData
mlc_finitely_renormalizable_of_paraPuzzleTransportExistsData
mlc_finitely_renormalizable
```

through the generic theorem where this is type-correct. Preserve their names
and statements.

### 3. Direct/main-route audit

Inspect:

- `Mlc/DirectRoute.lean`
- `Mlc/MainConjecture.lean`
- `Mlc/MoleculeConjectureBridge.lean`
- `Mlc/MoleculeToParameterShrink.lean`

For each theorem-facing use, classify it as:

- generic connected-window consumption;
- frozen para-puzzle source dependence;
- essential shrinkage/phase–parameter dependence.

Add only small, safe generic wrappers for the first category. Do not rewrite the
whole main theorem or fabricate a provider.

## Non-goals and constraints

- Do not prove the frozen straddling theorem.
- Do not construct Böttcher coordinates, parameter rays, or graph geometry.
- Do not add `sorry`, `admit`, or project axioms.
- Do not delete the frontier axiom.
- Preserve existing APIs and avoid unrelated edits.
- Do not commit.

## Verification

Run:

```bash
lake build
lake env lean check_axioms.lean
```

The project axiom frontier must remain unchanged.

## Report

Write the report to:

`plan/GPT54_RESULT_58_MIGRATE_FINITE_SIDE_TO_MOVING_WINDOW_INTERFACE.md`

Include:

- changed files and theorem names;
- a classification table for the audited consumers;
- what is now generic;
- the precise remaining concrete moving-window/provider package required before
  the frontier axiom can be deleted.
