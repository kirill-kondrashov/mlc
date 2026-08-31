# Prompt 109 — Parameter-loop transition comparison and cocycle gate

plan/GPT54_TASK_109_PARAMETER_LOOP_TRANSITION_COMPARISON.md

Result 108 constructs a finite root-of-unity product for one chosen closed-loop
chart chain. Before calling it monodromy, the repository needs a checked account
of how local transition factors compare. This prompt establishes the smallest
local comparison layer and then honestly audits whether the current path-chain
data suffices for refinement invariance.

In a focused module, preferably Mlc/ParameterCriticalOrbitLoopComparison.lean,
work from ParameterCriticalOrbitLocalBranchData.overlap_transition_common_level.
At a fixed common level L, implement a canonical transition multiplier for two
charts on a preconnected overlap W with chosen witness w0. Define it directly
from the quotient of the two nonzero branch values at w0. Prove:

- it lies in rootsOfUnitySet (2 ^ L);
- it gives the transition identity on all of W;
- it is unique among constants satisfying that identity on W.

Then prove the cocycle identity on a single preconnected triple-overlap set W:
for three charts D0, D1, D2 at a common level, the canonical transition from
D0 to D2 equals the product of the transitions from D0 to D1 and D1 to D2.
Use the common witness point and nonvanishing branches to pin the equality.

After that local theorem, audit the exact refinement comparison needed for the
finite product from Result 108. In particular, determine whether the current
ParameterPathMeshChain API supplies a connected transport set or a common
triple overlap linking an original edge to two refined edges. If it does, prove
the corresponding one-edge subdivision product identity. If it does not, define
the smallest explicit refinement-comparison data structure or record the exact
missing hypothesis. Do not silently treat pairwise overlap balls as a connected
triple overlap.

Do not prove general refinement invariance, chain-choice independence,
homotopy invariance, product equals 1, a monodromy representation, or a global
coordinate unless each is independently and concretely proved. This is a local
cocycle/comparison gate only.

Do not use mandelbrot_set_connected, external_ray_map_exists, the frozen
straddling axiom, global extension contracts, new axioms, sorry, or admit. Do
not commit. Run targeted Lean checks and lake build.

Write:

plan/GPT54_RESULT_109_PARAMETER_LOOP_TRANSITION_COMPARISON.md

## File-only worker handoff

All communication for this task is through repository files only. Do not expect
or request a pasted CLI response. Read this prompt, write source changes, and
write the required result file in plan. The result file must state whether the
targeted Lean check and lake build passed, include exact remaining errors if
blocked, and identify the next file-level handoff.
