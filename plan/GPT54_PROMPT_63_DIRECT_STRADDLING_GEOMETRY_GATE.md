Begin Stage 1 of the direct frozen-straddling proof sequence:

`plan/GPT54_TASK_63_DIRECT_STRADDLING_GEOMETRY_GATE.md`

The target remains:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
```

Do not use the frontier axiom, the old para-puzzle connectivity axiom, or any
moving-window provider.

Define or normalize the frozen set:

```lean
S c n := {c' : ℂ | green_function c (c' - c) < (1 / 2 : ℝ)^n}
```

Prove every elementary fact available from existing Green-function results:

- openness;
- translation equivalence with `GreenSublevel c n`;
- connectedness and boundedness;
- nonempty/basepoint membership for `c ∈ MandelbrotSet`;
- exact meaning of the straddling hypothesis;
- any valid fullness, path-connectedness, or boundary facts already justified
  by the repository.

Audit whether existing results can provide a direct reduction of
`IsConnected (S c n ∩ MandelbrotSet)` to a genuine specialized separation or
boundary lemma. Do not use the invalid general principle that intersections of
connected sets are connected.

If no nontrivial direct reduction is available, make no speculative edits and
report the first missing geometric lemma. If useful elementary definitions or
lemmas are proved, keep them focused and compile them.

No new axiom, `sorry`, `admit`, renamed frozen wrapper, or Böttcher scaffolding.
Do not delete the frontier axiom or modify the root theorem. Do not commit.

Write:

`plan/GPT54_RESULT_63_DIRECT_STRADDLING_GEOMETRY_GATE.md`
