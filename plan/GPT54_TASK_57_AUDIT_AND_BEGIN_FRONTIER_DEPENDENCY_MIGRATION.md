# TASK 57 — Audit and begin migration away from the frozen frontier axiom

## Global context

The live axiom is:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The exact frozen-base theorem has no verified source route in the repository.
The Böttcher replacement route is blocked at the instantiated whole-basin
extension:

```lean
LogSeriesBasinExtensionDataFor c
```

The credible alternative is to discharge the axiom from the dependency graph,
not to prove the artificial frozen set directly.

The repository now contains a corrected generic consumer:

```lean
ConnectedWindowParameterPieceData
ParameterPieceLcAtData
lc_at_of_connectednessWindow_family_data
```

but the downstream para-puzzle/main-path code still uses the frozen
`ParaPuzzlePieceAt` and its connectivity theorem.

## Deliverable

Audit the full dependency path from the frontier axiom to `mlc_conjecture`.
Search all source files and classify each use of:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
green_sublevel_translate_inter_mandelbrot_connected
ParaPuzzlePieceAt
para_puzzle_piece_inter_mandelbrot_connected
```

Produce a precise migration map identifying:

- direct axiom consumers;
- generic topology consumers;
- definitions that encode the frozen Green translate as an equality;
- shrinkage/LC consumers that can already accept a moving window;
- the smallest remaining theorem-facing seam.

If the seam is unambiguous, implement it in a focused module. A valid
implementation may introduce a new theorem route parameterized by
`ConnectedWindowParameterPieceData` and connect it to the existing
`LcAtOfShrink`/main-path consumers, while leaving all frozen compatibility
theorems and the axiom untouched.

If implementation would require a concrete moving-window theorem that is not
yet present, make no speculative source changes. State the exact minimal
future data package and which declarations must be migrated once it exists.

## Constraints

- Do not prove or assume the frozen straddling theorem.
- Do not fabricate parameter rays, Böttcher extensions, or moving families.
- Do not delete or weaken the frontier axiom.
- No `sorry`, `admit`, or new axiom.
- Do not edit unrelated Böttcher modules or commit.

## Verification

For any source changes, run:

```bash
lake build
lake env lean check_axioms.lean
```

The current axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_57_AUDIT_AND_BEGIN_FRONTIER_DEPENDENCY_MIGRATION.md`

Report the complete dependency map, any migration seam implemented, and the
precise remaining package needed before the frontier axiom can be deleted.
