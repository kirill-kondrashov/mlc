Continue Stage 3 of the direct frozen-straddling sequence:

`plan/GPT54_TASK_65_DIRECT_FROZEN_BOUNDARY_CROSSING_THEOREM.md`

Stages 1–2 should have isolated the exact missing no-separation property. Prove
that property for the frozen Green translate using actual quadratic Green
function and Mandelbrot geometry.

The target is a theorem strong enough to imply:

```lean
IsConnected
  ({c' | green_function c (c' - c) < (1 / 2 : ℝ)^n} ∩ MandelbrotSet)
```

in the straddling case.

Do not replace the frozen set by a genuine moving parapuzzle, and do not use
the frontier axiom indirectly through `ParaPuzzlePieceAt` or transport data.

If the proof requires a new classical theorem, state it precisely and explain
why it is not derivable from the current formalized facts. Do not encode that
theorem as an axiom. A hard-stop report is the correct result if the exact
frozen boundary-crossing statement has no valid direct proof.

Write:

`plan/GPT54_RESULT_65_DIRECT_FROZEN_BOUNDARY_CROSSING_THEOREM.md`
