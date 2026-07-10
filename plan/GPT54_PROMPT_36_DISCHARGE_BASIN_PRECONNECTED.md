Implement the task in
`plan/GPT54_TASK_36_DISCHARGE_BASIN_PRECONNECTED.md`.

Context: iteration 35 reduced `IsPreconnected (basin_of_infinity c)` to a single
per-level crux — `∀ n, IsPreconnected {z | R c < ‖orbit c z n‖}` — and landed the
reduction lemma `basin_preconnected_of_forall_superlevel_preconnected` in the new
leaf file `Mlc/BasinConnected.lean`. This task **discharges that crux
unconditionally**, closing the entire basin-preconnectedness residual of the
Böttcher route.

The crux is proved by a maximum-modulus argument that sidesteps
"complement-of-compact has no bounded components" (which Mathlib lacks). Each
superlevel set `U = {z | R c < ‖orbit c z n‖}` is open and contains the connected
far exterior `{z | R c < ‖z‖}`. If a separation `U ⊆ u ∪ v` split `U`, the
exterior lies wholly on one side, so the *other* side `U ∩ w` is bounded (it omits
the exterior). On that bounded open side the entire function `P = orbit c · n`
strictly exceeds `R c` inside while staying `≤ R c` on the frontier — impossible by
the maximum modulus principle (`Complex.exists_mem_frontier_isMaxOn_norm`).

The complete proof script in the task file is planner-verified to compile: I
inserted it into `Mlc/BasinConnected.lean`, ran a full `lake build`
(7873 jobs, green) and `lake env lean check_axioms.lean` (exit 0, frontier
unchanged), then reverted. Paste it verbatim.

Placement: APPEND the script to the EXISTING file `Mlc/BasinConnected.lean`,
immediately before its final `end MLC.Quadratic`. Do NOT create a new file, do
NOT touch the imports/`open` line, do NOT re-state the existing reduction lemma.

Steps:
(1) Append the seven declarations (`differentiable_orbit`,
`exterior_subset_superlevel`, `exterior_preconnected`, `maxmod_absurd`,
`frontier_side_subset_compl`, `isPreconnected_orbit_superlevel`,
`basin_of_infinity_isPreconnected`) verbatim before `end MLC.Quadratic`.
(2) `lake build` clean; no new `sorry`/`axiom`. (A single harmless
`linter.unnecessarySimpa` warning at the `exterior_preconnected` `simpa` line is
expected and acceptable — leave it.)
(3) Confirm the axiom frontier is still exactly the two project axioms
(`lake env lean check_axioms.lean`, exit 0).
(4) In the result, state that `basin_of_infinity_isPreconnected c :
IsPreconnected (basin_of_infinity c)` now holds **unconditionally** for every
`c`, discharging the basin residual entirely. Consequently the genuine
Böttcher-coordinate `conj` obligation (iteration 34,
`coherentBasinCoordinate_conj_of_holo_of_preconnected`) is now derivable, and the
ONLY remaining residual on the Böttcher route is `holo_on_basin`
(holomorphicity of the coherent branch).

Do NOT introduce `sorry`/`axiom`, do NOT edit `ConstructiveBasinCoordinate.lean`
or `ConstructiveBasinModulus.lean`, do NOT modify the existing reduction lemma or
the imports, and do NOT commit.

Write:

`plan/GPT54_RESULT_36_DISCHARGE_BASIN_PRECONNECTED.md`
