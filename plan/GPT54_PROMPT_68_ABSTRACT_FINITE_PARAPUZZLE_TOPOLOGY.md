Continue the source-first sequence with:

`plan/GPT54_TASK_68_ABSTRACT_FINITE_PARAPUZZLE_TOPOLOGY.md`

Use the sourced theorem and non-opaque contract from Result 67.

Formalize only the reusable finite planar topology needed before the quadratic
instantiation:

- finite embedded boundary arcs/graphs or an equivalent concrete boundary model;
- admissible parameter components/windows defined from those boundaries;
- openness of the selected component/window;
- basepoint membership;
- nesting and component-selection lemmas;
- a neighborhood-basis consequence when supplied with a genuine shrinkage
  hypothesis.

Do not define a structure whose fields simply restate
`ConnectednessWindowParameterPieceData`. The windows must be constructed from
the finite boundary/combinatorial model.

Do not claim Mandelbrot connectedness yet unless it follows from an actual
transport theorem. Preserve old frozen APIs and do not touch the frontier axiom.

If the necessary planar topology is not available in Mathlib, implement only
small proved lemmas or report the exact missing theorem. No axioms, `sorry`,
`admit`, fake rays, or identity “motions”. Do not commit.

Write:

`plan/GPT54_RESULT_68_ABSTRACT_FINITE_PARAPUZZLE_TOPOLOGY.md`
