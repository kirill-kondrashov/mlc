# Prompt 106 — Parameter-local chart overlap transitions

plan/GPT54_TASK_106_PARAMETER_LOCAL_CHART_OVERLAP_TRANSITIONS.md

Result 105 now provides ParameterCriticalOrbitLocalBranchData c0 and proves
that its branch has the critical-orbit root identity at every later finite
escape level. The next missing layer is the transition data between two such
local charts. This prompt is strictly local-on-overlap; it does not define
parameter paths, loops, global continuation, or trivial monodromy.

In Mlc/ParameterCriticalOrbitLocal.lean, formulate and prove a theorem of the
following kind. Let D0 and D1 be local chart data, let W be a connected set with
W subset of D0.V intersection D1.V, and let L be max D0.N D1.N. Prove that
there exists a constant xi such that:

~~~lean
xi in rootsOfUnitySet (2 ^ L)
forall c in W, D1.G c = xi * D0.G c
~~~

Equivalent formulations using the ratio D1.G c / D0.G c are acceptable. The
result must work after lifting both charts to the common level L using
ParameterCriticalOrbitLocalBranchData.root_eq_add.

Required proof ingredients:

1. rewrite both root identities at level L, so their 2^L powers equal the same
   logSeriesBottcherApprox value at orbit c 0 (L + 1);
2. prove both branch values are nonzero on W from the uniform exterior estimate
   and one_lt_norm_logSeriesBottcherApprox_of_outside_open;
3. show the quotient is a 2^L-th root of unity pointwise;
4. use differentiability or continuity of the quotient and connectedness of W
to prove that this root-of-unity-valued quotient is constant.

Use the most directly applicable checked finite/discrete-root topology lemma. If
that final connectedness-to-constancy step is not available, prove the smallest
reusable lemma for a continuous map from a connected set into a finite discrete
set, or record its exact missing Mathlib statement. Do not introduce an axiom.

Do not normalize xi to 1. A constant root-of-unity transition is the intended
local Cech-style cocycle datum; proving that products around loops are 1 is a
later, separate monodromy gate.

Do not use mandelbrot_set_connected, external_ray_map_exists, the frozen
straddling axiom, global extension contracts, new axioms, sorry, or admit. Do
not commit. Run targeted Lean checks and lake build.

Write:

plan/GPT54_RESULT_106_PARAMETER_LOCAL_CHART_OVERLAP_TRANSITIONS.md

The result must clearly distinguish a local constant overlap multiplier from
parameter-path continuation and global monodromy triviality.
