Implement the basin coherent-fields task in
`plan/GPT54_TASK_31_LAND_BASIN_COHERENT_FIELDS.md`.

Correction to Task 30: the Part A proofs must live DOWNSTREAM of `GreenHarmonic`
(which imports `ConstructiveBasinCoordinate`), not inside it — your import-cycle
finding was right, but the fix is placement, not a math blocker. All seven
theorems in the task file are VERIFIED to compile in the correct file.

Steps: (1) remove the four hypothesis-taking wrapper stubs you added to
`ConstructiveBasinCoordinate.lean` in Task 30 (they are the forbidden
property-bundle pattern). (2) create
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinModulus.lean` importing
`GreenHarmonic`, register it in `Mlc.lean`, and paste the seven verified theorems
verbatim (modulus, candidate modulus, norm>1, tendsto, escape-time recursion,
cpow squaring, conj_on_basin) — these discharge 5 of 7
`PrincipalPullbackCoherentDataFor` fields. (3) resolve the two genuinely open
fields: `basin_of_norm_gt_one` (likely needs revising the off-basin totality
branch of the candidate to norm ≤ 1) and `holo_on_basin` (the real
principal-cpow branch-cut crux — prove or pin exactly). (4) assemble
`PrincipalPullbackCoherentDataFor c` with no bundle shortcut, `lake build`, and
confirm no new `sorry`/`axiom`.

Write:

`plan/GPT54_RESULT_31_LAND_BASIN_COHERENT_FIELDS.md`

Do not reuse the proxy, do not close fields with property-bundle adapters or
hypotheses, do not introduce `sorry`/`axiom`, and do not commit. Stop once the
report is complete and the build is green.
