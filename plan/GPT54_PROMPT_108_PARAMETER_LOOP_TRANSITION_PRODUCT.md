# Prompt 108 — Finite parameter-loop transition product

plan/GPT54_TASK_108_PARAMETER_LOOP_TRANSITION_PRODUCT.md

Result 107 gives a finite ordered local-chart chain along any compact parameter
path in MandelbrotSet complement, with explicit adjacent preconnected overlap
neighborhoods. This prompt constructs the finite transition product for a
closed loop. It does not prove monodromy triviality or a global coordinate.

In a focused module, preferably Mlc/ParameterCriticalOrbitLoopProduct.lean,
define a closed parameter loop by extending ParameterPath with an endpoint
condition path 0 = path 1. Reuse ParameterPathFiniteLocalBranchCover and
ParameterPathMeshChain.

For the finite mesh chain of a loop:

1. choose or construct one natural number L at least every local chart level
   occurring in the finite chain. Use a finite maximum or an equivalent
   explicit bound; do not add a bound as an axiom;
2. add a common-level variant of overlap_transition if needed: for charts D0,
   D1, a preconnected overlap W with a witness, and L at least both chart
   levels, obtain a constant transition xi in rootsOfUnitySet (2 ^ L) with
   D1.G c = xi * D0.G c on W;
3. obtain one such multiplier for every adjacent mesh overlap, using the
   explicit balls from ParameterPathMeshChain.overlap_transition_data;
4. construct the closing overlap between the last and first chart using the
   loop endpoint equality and the relevant endpoint cells, again shrinking to
   an explicit open ball rather than assuming the raw intersection connected;
5. define the ordered product of all adjacent and closing multipliers, and
   prove its membership in rootsOfUnitySet (2 ^ L), or the closest checked
   equivalent finite-root statement.

Package the resulting finite data in a concrete structure if useful. It should
make the level, chain, individual multipliers, closing multiplier, and product
explicit enough for a later chain-independence and monodromy theorem.

Do not prove the product equals 1. Do not claim it is invariant under chart
choices, refinements, or loop homotopy. Do not call it a monodromy
representation unless its choice-independence and composition laws are actually
proved. Do not build a global parameter Böttcher coordinate or parameter rays.

Do not use mandelbrot_set_connected, external_ray_map_exists, the frozen
straddling axiom, global extension contracts, new axioms, sorry, or admit. Do
not commit. Run targeted Lean checks and lake build.

Write:

plan/GPT54_RESULT_108_PARAMETER_LOOP_TRANSITION_PRODUCT.md

The result must distinguish the constructed finite product from the still open
triviality, refinement invariance, and global continuation questions.

## File-only worker handoff

All communication for this task is through repository files only. Do not expect
or request a pasted CLI response. Read this prompt, write source changes, and
write the required result file in plan. The result file must state whether the
targeted Lean check and lake build passed, include exact remaining errors if
blocked, and identify the next file-level handoff.

## Current corrective note

The closing-basepoint issue has been repaired by choosing an explicit base chart
at path 0. The current draft fails only while proving that 1 lies in the final
mesh cell. In Mlc/ParameterCriticalOrbitLoopProduct.lean, replace the two simp
attempts in that proof with this positive-denominator calculation, adapting
names only if necessary:

~~~lean
have hpos : (0 : ℝ) < (chain.meshSize + 1 : ℝ) := by positivity
constructor
· calc
    (chain.meshSize : ℝ) / (chain.meshSize + 1 : ℝ)
        ≤ (chain.meshSize + 1 : ℝ) / (chain.meshSize + 1 : ℝ) := by
          exact div_le_div_of_nonneg_right
            (by exact_mod_cast Nat.le_succ chain.meshSize) hpos.le
    _ = 1 := div_self (ne_of_gt hpos)
· rw [div_self (ne_of_gt hpos)]
~~~

Then rerun the required checks and update the result file. This is a correction
to the active Prompt 108, not a new prompt and not permission to make any
monodromy-triviality claim.
