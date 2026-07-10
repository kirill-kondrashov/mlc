Implement the task in
`plan/GPT54_TASK_34_REDUCE_CONJ_TO_HOLO_AND_PRECONNECTED.md`.

Context: iteration 33 landed the coherent basin coordinate
`coherentBasinCoordinate d` and the constructor
`genuineBottcherCoordinateData_of_escapeTimeIndependent_of_conj_of_holo`, which
reduces `GenuineBottcherCoordinateDataFor c (coherentBasinCoordinate d)` to
exactly two residual facts: `conj_on_basin` and `holo_on_basin`. This task
discharges the **conjugacy** residual against holomorphicity, shrinking the seam
to `{holo, IsPreconnected basin}`.

Land ONE theorem, `coherentBasinCoordinate_conj_of_holo_of_preconnected`, in
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean` (inside its
existing `namespace MLC.Quadratic`). It proves: if the basin is preconnected and
the coordinate is `DifferentiableOn ℂ` on it, then the coordinate conjugates the
quadratic map to squaring on the whole basin. Mechanism: `φ∘f` and `φ²` are both
`AnalyticOnNhd` on the open basin and agree on the exterior collar (where
`φ = logSeriesBottcherApprox` and the local Böttcher functional equation holds),
so the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) forces global agreement.

The complete proof script in the task file is planner-verified to compile
(`lake env lean` probe, `PROBE_EXIT_0`) against the current tree. Paste it
verbatim.

Steps:
(1) Add the theorem verbatim; do not weaken hypotheses or generalize.
(2) `lake build` clean; no new `sorry`/`axiom`.
(3) Confirm the axiom frontier is still exactly the two project axioms
(`lake env lean check_axioms.lean`, exit 0).
(4) In the result, restate that the genuine-coordinate seam is now exactly
`{holo_on_basin, IsPreconnected (basin_of_infinity c)}` — both classical
Douady–Hubbard-depth facts — and note that `conj` is no longer an independent
residual.

Do NOT create a new file, edit `ConstructiveBasinCoordinate.lean`, introduce
`sorry`/`axiom`, bundle away `holo` or `IsPreconnected`, or commit. Stop once the
build is green and the report is complete.

Write:

`plan/GPT54_RESULT_34_REDUCE_CONJ_TO_HOLO_AND_PRECONNECTED.md`
