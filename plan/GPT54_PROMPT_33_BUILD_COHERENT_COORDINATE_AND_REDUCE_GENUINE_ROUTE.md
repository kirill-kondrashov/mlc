Implement the task in
`plan/GPT54_TASK_33_BUILD_COHERENT_COORDINATE_AND_REDUCE_GENUINE_ROUTE.md`.

Important correction to the iteration-32 result: `basinLogSeriesExtensionCandidate`
is the PRINCIPAL-branch pullback, which is provably NON-holomorphic on the basin
(it jumps by `exp(2πi/2^N)` where `logSeriesBottcherApprox` crosses `ℝ<0`). So
`principalPullbackCoherentData_of_holo` has an unsatisfiable hypothesis. Do NOT
touch that candidate and do NOT try to prove it holomorphic.

This task switches to the correct coordinate — the escape-time-independent
(branch-coherent) value already scaffolded as `EscapeTimeIndependentPullbackDataFor c`.
For it, the Böttcher modulus is automatic and holomorphicity is achievable.

All scripts in the task file are planner-verified to compile in
`ConstructiveBasinModulus.lean`. Steps:
(1) Land `escapeTimeIndependent_value_modulus`: any escape-time-independent value
has `‖value‖ = exp(green)` (from the root equation + modulus-at-infinity + Green
orbit scaling).
(2) Define `coherentBasinCoordinate d` (on-basin `d.value`, off-basin `0`) and its
`_on_basin` / `_extends_near` / `_modulus` identities.
(3) Land `genuineBottcherCoordinateData_of_escapeTimeIndependent_of_conj_of_holo`:
a constructor reducing `GenuineBottcherCoordinateDataFor c (coherentBasinCoordinate d)`
to exactly two explicit hypotheses — `conj_on_basin` and `holo_on_basin` — proving
the other five conjuncts (norm, basin characterization, modulus, continuity,
normalization) automatically.
(4) `lake build`, no new `sorry`/`axiom`, and confirm the axiom frontier is still
exactly the two project axioms.
(5) Report the residual seam (`conj` + `holo`) and the future reductions
(conj⟸holo via identity theorem on the preconnected basin; holo via the
monodromy-coherence machinery).

All declarations go in `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean`
(inside `namespace MLC.Quadratic`). Do NOT create a new file or edit
`ConstructiveBasinCoordinate.lean`.

Write:

`plan/GPT54_RESULT_33_BUILD_COHERENT_COORDINATE_AND_REDUCE_GENUINE_ROUTE.md`

Do not introduce `sorry`/`axiom`, do not stub or bundle away `conj`/`holo`, do not
use property-bundle adapters, and do not commit. Stop once the build is green and
the report is complete.
