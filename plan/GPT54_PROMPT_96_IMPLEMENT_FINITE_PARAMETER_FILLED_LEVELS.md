# Gated -- run only after Results 94 and 95

`plan/GPT54_TASK_96_IMPLEMENT_FINITE_PARAMETER_FILLED_LEVELS.md`

Implement the finite filled parameter level package:

```lean
def ParameterFilledLevel (n : ℕ) : Set ℂ :=
  {c : ℂ | ‖orbit c 0 (n + 1)‖ ≤ 2}
```

Using the completed critical-value and closed-lemniscate results, prove:

1. compactness of every level;
2. decreasing nesting;
3. `MandelbrotSet = ⋂ n, ParameterFilledLevel n`;
4. `IsConnected (ParameterFilledLevel n)`.

Do not use `mandelbrot_set_connected`, a parameter coordinate, external rays,
the straddling axiom, new axioms, `sorry`, or `admit`. Then update the
existing Prompt 90 gate only if all four theorems compile. Do not commit.

Write:

`plan/GPT54_RESULT_96_IMPLEMENT_FINITE_PARAMETER_FILLED_LEVELS.md`
