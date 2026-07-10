Complete the active-frontier task in
`plan/GPT54_TASK_42_PROVE_LOCAL_ROOT_BRANCH_OVERLAP_EQUALITY.md`.

Result 41 established that the moving-parameter route is blocked by the absence
of a genuine whole-basin Böttcher extension. Do not try to jump directly to
that global extension, and do not relabel the proxy or principal-`cpow`
candidate as a Böttcher coordinate. The next smallest honest step is the local
overlap lemma needed before any monodromy argument:

> Two finite-level holomorphic root branches solving the same nonvanishing
> pullback equation agree throughout a connected overlap if they agree at one
> overlap point.

Audit and reuse the existing algebraic and analytic infrastructure in
`ConstructiveBasinCoordinate.lean`, especially:

- `pullbackRootSet_torsor_transitive`;
- `rootsOfUnitySet`;
- `LocalPullbackRootBranchData`;
- `ConnectedAnalyticZeroFreeChartRootBranchData.rootBranch_eq_of_eqAt`;
- the Stage 1–2C modules
  `BottcherLocalRootBranch`,
  `BottcherFiniteLevelCoherence`,
  `BottcherArbitraryFiniteLevelLift`, and
  `BottcherFiniteEscapingLoopCover`.

Implement a focused new module only if a sound theorem can be stated and
compiled. The theorem should be generic enough to apply to two
`LocalPullbackRootBranchData c N ...` branches on a connected overlap, while
making the nonvanishing/outside hypothesis explicit rather than smuggling it
through a fragile definition. A suitable shape is an `EqOn` conclusion from:

- a connected/preconnected overlap;
- overlap inclusion in both branch domains;
- a point in the overlap where the branches agree;
- nonvanishing of the common pullback target on the overlap.

The proof may use the continuous ratio of the two nonzero branches and the
finite roots-of-unity range, or an existing connected analytic chart theorem.
Do not require the impossible all-level chart-chain structure and do not claim
that this proves monodromy triviality.

If the generic overlap theorem cannot be proved from current Mathlib/repository
APIs, do not add an abstract axiom, `sorry`, or a misleading weaker theorem.
Instead report the exact first missing topology/algebra lemma and the smallest
repair task.

Write the worker report to:

`plan/GPT54_RESULT_42_PROVE_LOCAL_ROOT_BRANCH_OVERLAP_EQUALITY.md`

Do not edit unrelated files, do not modify the frontier axiom, do not resume
parameter rays/equipotentials, and do not commit.
