Continue only after Result 77:

`plan/GPT54_TASK_78_PROVE_FULL_COMPACT_COMPLEMENT_SIMPLY_CONNECTED.md`

Prove the generic planar theorem needed for the parameter exterior:

> If `K ⊆ ℂ` is compact and full in the precise selected sense, then
> `Kᶜ` is simply connected (with the exact Lean notion used by the project).

Use existing Mathlib topology/complex-analysis results where possible. If
Mathlib lacks the bridge, formalize the smallest genuine planar theorem needed,
not an opaque structure whose field is already simple connectedness.

Do not specialize to Mandelbrot yet and do not use an external coordinate or
Riemann map as an assumption. If the theorem is not realistically derivable
from the current library without a substantial missing planar-topology
development, stop and report that exact gap.

No new axiom, `sorry`, `admit`, or frontier-axiom use. Do not commit.

Write:

`plan/GPT54_RESULT_78_PROVE_FULL_COMPACT_COMPLEMENT_SIMPLY_CONNECTED.md`
