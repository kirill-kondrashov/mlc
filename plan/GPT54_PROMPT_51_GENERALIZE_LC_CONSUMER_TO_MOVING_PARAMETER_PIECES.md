Complete the active-frontier task in
`plan/GPT54_TASK_51_GENERALIZE_LC_CONSUMER_TO_MOVING_PARAMETER_PIECES.md`.

Global strategy has now been reassessed. The exact frozen-base theorem has no
verified classical route, while the credible path is to replace the frozen
`ParaPuzzlePieceAt` object by a genuine moving-parameter piece family and then
remove the frontier axiom from the dependency graph.

Before formalizing parameter rays or a parameter external coordinate, decouple
the local-connectivity consumer from the frozen surrogate. Generalize the
generic topology in `Mlc/LcAtOfShrink.lean` to an independently supplied
depth-indexed parameter-piece family.

Introduce a focused, non-axiomatic consumer interface for a family
`P : ℂ → ℕ → Set ℂ` containing only the hypotheses actually needed by the
local-connectivity proof:

- the pieces are open;
- the base parameter belongs to every piece;
- the pieces form a neighborhood basis at the base parameter (either prove this
  from a clearly stated compact/nested/shrink package or expose it as an
  explicit theorem input);
- `P c n ∩ MandelbrotSet` is connected;
- the family shrinks to `{c}` where required.

Then prove the generic analogue of:

```lean
lc_at_of_shrink_of_data
```

with `P` in place of `ParaPuzzlePieceAt`. Preserve the current frozen theorem
as a compatibility specialization; do not delete or rewrite the frontier axiom
yet. The new theorem must be usable later with a genuine connectedness-locus or
moving parapuzzle family.

Keep the interface honest: do not define `P` by the frozen Green translate, do
not store an `IsConnected` witness as the definition of the piece, and do not
claim that a concrete moving family already exists. This task is consumer
migration infrastructure, not the parameter-geometry proof.

Write the worker report to:

`plan/GPT54_RESULT_51_GENERALIZE_LC_CONSUMER_TO_MOVING_PARAMETER_PIECES.md`

Do not resume the Böttcher mesh/monodromy sequence in this task. Do not add
`sorry`, `admit`, or new axioms, do not edit unrelated files, and do not commit.
