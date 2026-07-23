Continue the moving-parapuzzle route from the completed finite graph foundation:

`plan/GPT54_TASK_74_INSTANTIATE_QUADRATIC_PARAPUZZLE_BOUNDARIES.md`

Result 73 added and validated:

`Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`

It provides concrete finite embedded arcs, closed carriers, selected
complementary components, and refinement nesting. Now audit and, if possible,
instantiate those arcs with actual quadratic finite parapuzzle boundary data.

Inspect existing modules for proved ingredients:

- external/parameter ray maps;
- rational-angle combinatorics;
- equipotential arcs or Green-level curves;
- landing or endpoint theorems;
- finite graph incidence/no-crossing/refinement;
- Böttcher ray inversions or near-infinity parametrizations.

If a genuine finite ray/equipotential arc is already available, implement the
smallest constructor into `BoundaryArc` and prove its continuity, injectivity,
endpoint/incidence compatibility, and refinement properties.

If only partial ingredients exist, implement only the genuinely proved finite
combinatorial layer and report the first missing analytic/geometric theorem.
Do not create an arbitrary arc shell whose fields restate the desired facts.

Hard constraints:

- no `green_sublevel_translate_inter_mandelbrot_connected_straddling`;
- no `ParaPuzzlePieceAt` alias;
- no identity or `True` motion;
- no unproved ray landing, external coordinate, or phase–parameter theorem;
- no new axiom, `sorry`, or `admit`;
- do not claim Mandelbrot-slice connectedness yet;
- preserve existing APIs and do not commit.

Run targeted Lean checks and, for source changes:

```bash
lake build
lake env lean check_axioms.lean
```

Write:

`plan/GPT54_RESULT_74_INSTANTIATE_QUADRATIC_PARAPUZZLE_BOUNDARIES.md`
