# Prompt 107 — Finite parameter-path chart chain

plan/GPT54_TASK_107_PARAMETER_PATH_CHART_CHAIN.md

Result 106 now proves constant root-of-unity transition multipliers on a
preconnected overlap of two ParameterCriticalOrbitLocalBranchData charts. The
next missing layer is not monodromy triviality: it is the finite ordered chart
chain needed to transport these local transitions along a compact parameter
path in MandelbrotSet complement.

Implement or precisely audit the following finite-chain construction in a
focused module, preferably Mlc/ParameterCriticalOrbitPathChain.lean. Use the
most natural existing Lean representation of a continuous path on the compact
unit interval. Assume only that its image lies in MandelbrotSet complement.

For each path point, obtain ParameterCriticalOrbitLocalBranchData from
exists_parameterCriticalOrbitLocalBranchData. Then use openness of the chart
sets and compactness of the interval to produce finite ordered data containing:

- finitely many parameter chart data objects;
- a finite ordered subdivision of the interval or an equivalent interval mesh;
- each path segment contained in the corresponding chart set;
- for every adjacent pair, an explicit parameter point lying in both chart
  sets;
- a preconnected overlap neighborhood contained in both chart sets and
  containing that witness point, suitable as W for
  ParameterCriticalOrbitLocalBranchData.overlap_transition.

The local charts carry arbitrary open sets V. On an adjacent witness point,
shrink using the two chart openness proofs to an explicit metric ball contained
in their intersection; use convexity of a ball to obtain the required
preconnected overlap. Do not presume an arbitrary intersection is connected.

Reuse existing interval-mesh or Lebesgue-number infrastructure if it matches
the parameter-path setting. If the repository only has fixed-parameter
phase-space loop covers, do not identify it with this target without a checked
bridge. If the finite ordered compact-path cover is blocked, record the exact
smallest missing Mathlib or repository lemma rather than creating an axiom.

Do not multiply transition factors, define a loop monodromy representation,
claim a global coordinate, use parameter rays, or assert any triviality of
monodromy. This prompt ends with a finite chart-chain construction only.

Do not use mandelbrot_set_connected, external_ray_map_exists, the frozen
straddling axiom, global extension contracts, new axioms, sorry, or admit. Do
not commit. Run targeted Lean checks and lake build.

Write:

plan/GPT54_RESULT_107_PARAMETER_PATH_CHART_CHAIN.md

The result must separate the finite compact-path cover from the later
transition-product and closed-loop monodromy arguments.
