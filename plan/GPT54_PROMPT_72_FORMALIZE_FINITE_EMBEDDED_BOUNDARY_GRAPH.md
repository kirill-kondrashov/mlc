Replace the blocked abstract Stage 68 with the concrete foundational task:

`plan/GPT54_TASK_72_FORMALIZE_FINITE_EMBEDDED_BOUNDARY_GRAPH.md`

Result 68 identified the first implementable source-side module:
finite embedded boundary graphs and selected complementary components. Do not
attempt Mandelbrot connectedness or phase–parameter transport yet.

Build a focused module, preferably:

`Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`

with a non-opaque finite boundary model. A suitable design uses:

- finitely many continuous injective arcs `Icc (0 : ℝ) 1 → ℂ`;
- explicit endpoint/incidence compatibility;
- pairwise disjoint arc interiors or an equivalent no-crossing condition;
- the carrier as the finite union of arc images.

Prove:

1. each arc image is compact/closed;
2. the finite carrier is closed;
3. its complement is open;
4. for a basepoint outside the carrier, the selected component
   `connectedComponentIn carrierᶜ basepoint` is open and contains the
   basepoint;
5. if a refined graph has carrier inclusion and the same basepoint lies in both
   complements, the selected refined component is contained in the selected
   coarse component;
6. package the resulting window/nesting facts for a depth-indexed graph family.

Use existing Mathlib connected-component and compactness lemmas. Do not assert
Jordan separation, boundedness, or parapuzzle meaning unless proved.

This module must be genuinely geometric: do not define an arbitrary `Set ℂ`
with `IsClosed`/`IsOpen` fields that merely restate the conclusions, and do not
use `True` placeholders.

Constraints:

- no `green_sublevel_translate_inter_mandelbrot_connected_straddling`;
- no `ParaPuzzlePieceAt` alias;
- no phase–parameter theorem yet;
- no new axiom, `sorry`, or `admit`;
- preserve existing APIs and do not commit.

Run targeted Lean checks and write:

`plan/GPT54_RESULT_72_FORMALIZE_FINITE_EMBEDDED_BOUNDARY_GRAPH.md`
