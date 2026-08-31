Complete the active-frontier task in
`plan/GPT54_TASK_53_SEPARATE_OPEN_WINDOW_FROM_CONNECTEDNESS_LOCUS.md`.

Result 52 exposed an important global/API issue. The new
`connectednessLocusParameterPiece` is defined honestly, but the generic
local-connectivity consumer requires each neighborhood piece to be open. A
connectedness locus `M(g)` is generally a closed/full subset, not an ambient
open parameter piece, so treating the locus itself as the consumer’s open piece
is the wrong geometry.

Correct the moving-parameter abstraction by separating:

1. an ambient open finite-level parameter window/component `W n`;
2. the moving-family connectedness locus `K n` inside that window;
3. the relative set `W n ∩ MandelbrotSet` consumed by local connectivity.

Audit the declarations added in Result 51/52 and implement the smallest honest
correction. The generic consumer should receive an open family `W`, while the
connectedness theorem should concern `W n ∩ MandelbrotSet` (or an explicitly
equivalent relative connected subset). Keep `connectednessLocusParameterPiece`
as a separate definition if useful, but do not require it to be open.

Add:

- a corrected window/locus data structure or adapter;
- membership and inclusion lemmas relating `K n` to `W n`;
- a generic local-connectivity theorem using the open window family;
- compatibility with the current frozen `ParaPuzzlePieceAt` route where
  possible, without changing the frontier axiom.

Do not assert that the incomplete analytic quadratic-like core already supplies
open windows, connectedness, nesting, or shrinkage. If a proposed correction
requires a theorem not present in the repository, expose it as an explicit
hypothesis and report the missing sourced foundation.

Write the worker report to:

`plan/GPT54_RESULT_53_SEPARATE_OPEN_WINDOW_FROM_CONNECTEDNESS_LOCUS.md`

Do not resume Böttcher mesh/monodromy work. Do not add `sorry`, `admit`, or new
axioms, do not edit unrelated files, and do not commit.
