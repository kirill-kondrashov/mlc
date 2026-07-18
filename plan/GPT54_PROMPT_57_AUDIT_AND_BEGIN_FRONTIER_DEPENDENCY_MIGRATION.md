Complete the active-frontier task in
`plan/GPT54_TASK_57_AUDIT_AND_BEGIN_FRONTIER_DEPENDENCY_MIGRATION.md`.

Result 56 is decisive: the checked repository cannot currently construct the
whole-basin Böttcher extension needed for `Φ_M(c)=B_c(c)`. Do not continue
building local Böttcher scaffolding or parameter-graph shells.

Pivot to the only remaining credible discharge meaning: remove
`MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling` from the
dependency graph by migrating consumers from the frozen `ParaPuzzlePieceAt`
surrogate to the corrected moving-window interface.

First audit every direct and transitive use of:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
green_sublevel_translate_inter_mandelbrot_connected
ParaPuzzlePieceAt
para_puzzle_piece_inter_mandelbrot_connected
```

Map which uses are:

1. genuinely tied to the frozen Green-translate equality;
2. generic topology that can consume `ConnectedWindowParameterPieceData`;
3. theorem-facing wrappers that can be generalized without changing
   mathematical content.

Then implement the smallest real migration seam, if one is unambiguous:

- preserve the old frozen APIs for compatibility;
- add a new theorem-facing route whose hypotheses are supplied by a genuine
  moving-window family;
- prove that this route feeds the existing local-connectivity/main-path
  consumers without invoking the frozen straddling axiom.

Do not claim the axiom is removable until all downstream dependencies are
accounted for. If no safe source migration can be implemented before a concrete
moving-window theorem exists, make no speculative edits and report the exact
minimal migration package required.

Write the worker report to:

`plan/GPT54_RESULT_57_AUDIT_AND_BEGIN_FRONTIER_DEPENDENCY_MIGRATION.md`

Do not add `sorry`, `admit`, or axioms. Do not resume Böttcher mesh/monodromy
work, do not fabricate a moving family, do not delete the frontier axiom yet,
and do not commit.
