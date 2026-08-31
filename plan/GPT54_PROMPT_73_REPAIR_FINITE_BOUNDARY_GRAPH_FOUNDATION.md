Continue the concrete finite-boundary foundation from Result 72:

`plan/GPT54_TASK_73_REPAIR_FINITE_BOUNDARY_GRAPH_FOUNDATION.md`

Do not move to phase–parameter transport yet. Repair and complete the finite
embedded boundary graph module identified in:

`Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`

Resolve the exact blockers from Result 72:

1. Prove compactness/closedness of an arc range from a continuous map
   `Icc (0 : ℝ) 1 → ℂ`, using the exact Mathlib image/range normalization
   rather than an unproved simp claim.
2. Prove closedness of the finite carrier using an explicit `Finset` induction
   or the correct finite-union API.
3. Establish that connected components of open subsets of `ℂ` are open using
   an existing `LocallyConnectedSpace ℂ` theorem/instance if available, or
   prove the smallest local theorem from the metric/vector-space foundations.
   Do not add this as an axiom.
4. Prove selected-component nesting under carrier inclusion and common
   basepoint complement membership with explicit set-level intermediate lemmas.

Keep the model genuinely geometric:

- finite continuous injective arcs;
- concrete carrier as a finite union of arc images;
- selected component of the carrier complement.

Do not add Jordan separation, boundedness, ray landing, Mandelbrot
connectedness, or phase–parameter semantics in this task.

No `green_sublevel_translate_inter_mandelbrot_connected_straddling`,
`ParaPuzzlePieceAt` alias, new axiom, `sorry`, `admit`, or placeholder fields.
Preserve existing APIs and do not commit.

Run:

```bash
lake env lean Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean
lake build
lake env lean check_axioms.lean
```

Write:

`plan/GPT54_RESULT_73_REPAIR_FINITE_BOUNDARY_GRAPH_FOUNDATION.md`
