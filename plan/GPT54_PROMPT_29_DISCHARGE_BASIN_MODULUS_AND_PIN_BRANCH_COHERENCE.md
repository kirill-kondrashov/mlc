Complete the branch-coherence audit in
`plan/GPT54_TASK_29_DISCHARGE_BASIN_MODULUS_AND_PIN_BRANCH_COHERENCE.md`.

Global objective: discharge the frontier axiom
`green_sublevel_translate_inter_mandelbrot_connected_straddling` (one of exactly
two remaining `mlc_conjecture` axioms) via the Böttcher route, whose downstream
consumer is the parameter family `GenuineBottcherLocalParameterFamilyData`. This
task advances discharge item 1 of 4 (the full-basin monodromy-coherent
coordinate).

Start from the corrected baseline: the basin modulus identity
`‖principalPullbackLogSeriesBottcher c z‖ = exp(green_function c z)` is provable
NOW on the whole basin for arbitrary `c` (Result 28 wrongly called it a missing
hypothesis). First discharge the now-provable fields of
`PrincipalPullbackCoherentDataFor` (modulus, norm, extends_near,
tendsto_div_atInfinity) as genuine `/tmp` proofs for arbitrary `c`, map them onto
the parameter-family fields, then isolate and pin the branch-coherence crux:
escape-time independence and the holomorphic semiconjugacy of the principal-root
pullback across `basinEscapeTime` level sets. Write:

`plan/GPT54_RESULT_29_DISCHARGE_BASIN_MODULUS_AND_PIN_BRANCH_COHERENCE.md`

Do not close any field by a bundle-to-bundle adapter, do not reuse the proxy,
do not edit repository sources or other plan artifacts, and do not commit. Use
`/tmp` for Lean probes. Stop once the result report is complete.
