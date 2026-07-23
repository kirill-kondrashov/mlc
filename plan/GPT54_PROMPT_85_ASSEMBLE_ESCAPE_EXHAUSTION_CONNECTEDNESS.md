Run only after Results 86 and 87 provide checked proofs that the finite escape
levels are open, nested, exhaust `MandelbrotSetᶜ`, and are connected:

`plan/GPT54_TASK_85_ASSEMBLE_ESCAPE_EXHAUSTION_CONNECTEDNESS.md`

Use the exact existing Mathlib connected-union theorem for a nested chain to
derive:

```lean
theorem mandelbrotSet_compl_isConnected :
  IsConnected (MandelbrotSetᶜ)
```

Keep the proof restricted to the checked finite escape-level results. Add a
project-local fullness definition only if it is necessary and non-duplicative;
otherwise state the complement-connectedness theorem directly.

Do not claim `IsSimplyConnected`, an exterior coordinate, external rays, a
finite parapuzzle boundary arc, or the moving-window provider. Do not use the
frozen straddling axiom, `external_ray_map_exists`, a new axiom, `sorry`, or
`admit`. Do not commit.

Write:

`plan/GPT54_RESULT_85_ASSEMBLE_ESCAPE_EXHAUSTION_CONNECTEDNESS.md`
