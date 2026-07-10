Implement the task in
`plan/GPT54_TASK_38_FINITE_LEVEL_ROOT_COHERENCE.md`.

Feasibility result: the original Stage-2 plan “use simple-connectivity of the
basin to kill monodromy” is not a valid direct route. The plane basin is already
an exterior domain for `c = 0`, and the existing all-level
`BasinLoopChartChainMonodromyData` is impossible at `c = 2`, basepoint `0`,
level `N = 0` because `logSeriesBottcherApprox 2 0 = 0` while its charts are
zero-free. These blockers were formally verified. Mathlib's covering-space
lift API exists, but it does not remove the dynamical winding/divisibility
problem.

The corrected next step is **Stage 2A: finite-level coherence**. Add the
verified `LocalPullbackRootBranchData.lift_one_level` construction, expose that
the Stage-1 neighborhood stays in the escaping region, and provide the
Stage-1-specific lifted branch at level `N + 1`.

Create `Mlc/BottcherFiniteLevelCoherence.lean`, register it in `Mlc.lean`
immediately after `import Mlc.BottcherLocalRootBranch`, and paste the task's
verbatim script. Do not edit the Stage-1 or large scaffolding files. Run the
full build and `check_axioms.lean` (exit 0). Do not add `sorry`/`axiom` and do
not commit.

The result must say precisely that finite-level local compatibility is landed,
but global monodromy triviality, a coherent global basin value, and
`holo_on_basin` remain open. Write:

`plan/GPT54_RESULT_38_FINITE_LEVEL_ROOT_COHERENCE.md`
