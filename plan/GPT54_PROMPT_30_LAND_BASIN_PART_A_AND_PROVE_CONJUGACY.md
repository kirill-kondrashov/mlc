Implement the basin coordinate task in
`plan/GPT54_TASK_30_LAND_BASIN_PART_A_AND_PROVE_CONJUGACY.md`.

This is an IMPLEMENTATION task (mode change from the read-only audits 27–29). Edit
`Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`, run `lake
build`, and confirm no new `sorry`/`axiom`. Do not commit.

Global objective: populate `MLC.Quadratic.PrincipalPullbackCoherentDataFor c` for
arbitrary `c` (discharge item 1 toward the frontier axiom
`green_sublevel_translate_inter_mandelbrot_connected_straddling`, feeding
`GenuineBottcherLocalParameterFamilyData`).

Steps: (A) land the four already-proved Part A theorems supplied verbatim in the
task (modulus, candidate modulus, norm>1, tendsto — these compile as-is; Result 29
wrongly claimed they did not). (B) prove `conj_on_basin` via the escape-time
recursion `basinEscapeTime (f z) = N−1` plus the `cpow` identity `(x^w)^2 =
x^(2w)` and the exterior functional equation — this is bookkeeping, NOT monodromy.
(C) prove or precisely pin the genuine crux `holo_on_basin` (principal-cpow branch
cut across escape-time bands) and `basin_of_norm_gt_one`. (D) assemble
`PrincipalPullbackCoherentDataFor c` with no bundle-to-bundle shortcut and verify
the build.

Write:

`plan/GPT54_RESULT_30_LAND_BASIN_PART_A_AND_PROVE_CONJUGACY.md`

Do not reuse the proxy, do not close fields with property-bundle adapters, do not
introduce `sorry`/`axiom`, and do not commit. Stop once the result report is
complete and the build is green.
