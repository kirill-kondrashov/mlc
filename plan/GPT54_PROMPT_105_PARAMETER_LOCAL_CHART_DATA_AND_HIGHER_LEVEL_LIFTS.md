# Prompt 105 — Parameter-local chart data and all higher-level lifts

plan/GPT54_TASK_105_PARAMETER_LOCAL_CHART_DATA_AND_HIGHER_LEVEL_LIFTS.md

Results 104 and 101 now prove, for each c0 outside MandelbrotSet, a local
parameter branch G at an escape level N, together with the same-branch identity
at N + 1. Result 102 correctly found that parameter-loop monodromy cannot even
be formulated from these existential witnesses alone. The next honest step is
to package local charts and prove their finite higher-level coherence.

In Mlc/ParameterCriticalOrbitLocal.lean, define a concrete structure, preferably
ParameterCriticalOrbitLocalBranchData c0, containing at least:

- an escape level N, an open parameter set V, and a branch G;
- V in the neighborhood filter of c0 and IsOpen V;
- DifferentiableOn complex G V;
- the uniform exterior condition for orbit c 0 (N + 1) on V;
- the level-N root identity for G on V.

Construct this data without new assumptions from c0 not in MandelbrotSet by
reusing exists_parameterCriticalOrbitLocalRootBranch_coherentSucc or its proof.

Then prove a checked finite-lift theorem of the form:

~~~lean
theorem ParameterCriticalOrbitLocalBranchData.root_eq_add
    (D : ParameterCriticalOrbitLocalBranchData c0) (k : Nat) :
    forall c in D.V,
      (D.G c) ^ (2 ^ (D.N + k)) =
        logSeriesBottcherApprox c (orbit c 0 (D.N + k + 1))
~~~

Minor equivalent indexing is fine. Prove it by induction from the root identity,
the uniform exterior condition, forward invariance of the checked outside-open
region, and logSeriesBottcherApprox_iterate_succ_eq_sq. If the exact
forward-invariance lemma is missing, identify its precise checked name or
record the smallest concrete missing lemma; do not introduce an axiom.

The purpose is a reusable local chart whose branch is coherent at every common
future escape level. It is preparatory to a later overlap-transition theorem.
Do not define parameter loops, assert any overlap multiplier, claim analytic
continuation or trivial monodromy, build a global coordinate, or send the flow
to parameter rays.

Do not use mandelbrot_set_connected, external_ray_map_exists, the frozen
straddling axiom, global extension contracts, new axioms, sorry, or admit. Do
not commit.

Run targeted Lean checks and lake build. Write:

plan/GPT54_RESULT_105_PARAMETER_LOCAL_CHART_DATA_AND_HIGHER_LEVEL_LIFTS.md

The result must distinguish local all-future-level coherence from the still
unproved parameter-overlap and parameter-loop continuation layers.
