Implement the task in
`plan/GPT54_TASK_32_LAND_NORM_FIELD_AND_REDUCE_COHERENT_DATA_TO_HOLO.md`.

Result 31 was correct and honest: 5 of 7 `PrincipalPullbackCoherentDataFor`
fields are landed in `ConstructiveBasinModulus.lean`, build green, no new
sorry/axiom. This task closes a sixth field and pins the whole target to one
hypothesis.

DO NOT pursue the bandwise-`cpow` route you proposed for `holo_on_basin`. It is
provably impossible: every Mathlib `cpow_const` differentiability lemma requires
the base `∈ Complex.slitPlane`, but `logSeriesBottcherApprox` takes `ℝ<0` values
on the exterior (it is asymptotic to the identity), so the principal candidate
has genuine jump discontinuities in the basin. `holo_on_basin` needs the
monodromy-coherent construction, not this candidate — leave it as an explicit
hypothesis.

Steps (all scripts are planner-verified to compile):
(1) In `ConstructiveBasinCoordinate.lean`, change the off-basin branch of
`basinLogSeriesExtensionCandidate` from `MLC.logSeriesBottcherApprox c z` to `0`
(on-basin proofs are unaffected; full build stays green).
(2) Add `basinLogSeriesExtensionCandidate_basin_of_norm_gt_one` to
`ConstructiveBasinModulus.lean` (verified script in the task file) — this is the
sixth field.
(3) Add `principalPullbackCoherentData_of_holo`, a constructor that builds the
full `PrincipalPullbackCoherentDataFor c` from the six landed field theorems plus
a single `holo_on_basin` hypothesis (verified script in the task file).
(4) `lake build`, confirm no new `sorry`/`axiom`, and confirm the axiom frontier
is still exactly the two expected axioms.
(5) Write an honest `holo_on_basin` section: the slit-plane obstruction, the
genuine monodromy-coherence route, and which scaffolding structures already
exist in-repo.

Write:

`plan/GPT54_RESULT_32_LAND_NORM_FIELD_AND_REDUCE_COHERENT_DATA_TO_HOLO.md`

Do not introduce `sorry`/`axiom`, do not stub or fake `holo_on_basin`, do not use
property-bundle adapters, and do not commit. Stop once the build is green and the
report is complete.
