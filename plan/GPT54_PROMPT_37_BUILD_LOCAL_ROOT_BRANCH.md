Implement the task in
`plan/GPT54_TASK_37_BUILD_LOCAL_ROOT_BRANCH.md`.

Context: iterations 35–36 discharged basin preconnectedness *unconditionally*
(`basin_of_infinity_isPreconnected`). The sole remaining Böttcher-route residual
for the coherent coordinate is `holo_on_basin`. The *literal* candidate
`basinLogSeriesExtensionCandidate` is provably DISCONTINUOUS (principal-`cpow`
branch cut; verified at `c = 0`), so `holo_on_basin` is FALSE for it. The fix is
a coherent redefinition built from **local** holomorphic root branches glued by
killing monodromy. This task lands the reusable building block — **Stage 1 of
3** — as the existing `LocalPullbackRootBranchData c N z₀` structure.

Deliverable: a NEW leaf file `Mlc/BottcherLocalRootBranch.lean` with three
declarations (`differentiable_quadratic_iterate`, `mem_basin_of_iterate_mem_basin`,
`localPullbackRootBranchData_of_iterate_outside`), registered in `Mlc.lean`. The
complete proof script in the task file is planner-verified: it was placed in-repo,
a full `lake build` (7983 jobs, green) and `lake env lean check_axioms.lean`
(exit 0, frontier unchanged) both passed, then it was reverted. Paste it
verbatim.

Placement: CREATE `Mlc/BottcherLocalRootBranch.lean` with the verbatim content;
add `import Mlc.BottcherLocalRootBranch` in `Mlc.lean` right after `import
Mlc.BasinConnected`. Do NOT edit `ConstructiveBasinCoordinate.lean`,
`ConstructiveBasinModulus.lean`, `BottcherCpowSlit.lean`, or any other existing
file.

Steps:
(1) Create the leaf file verbatim; add the one import line to `Mlc.lean`.
(2) `lake build` clean; no new `sorry`/`axiom`.
(3) `lake env lean check_axioms.lean` exit 0 — frontier still exactly the two
    project axioms.
(4) In the result, state that Stage 1 (local holomorphic root branches,
    `LocalPullbackRootBranchData` populated via
    `localPullbackRootBranchData_of_iterate_outside`) is landed; and state
    clearly that this does NOT repair the discontinuous literal candidate and
    does NOT discharge `holo_on_basin` — Stage 2 (coherent global value via
    monodromy triviality) and Stage 3 (assembly) remain, and even finishing all
    three closes only `holo_on_basin`, with three further Yoccoz-scale pieces of
    the parameter-plane axiom beyond that.

Do NOT introduce `sorry`/`axiom`, do NOT edit `ConstructiveBasinCoordinate.lean`
or `ConstructiveBasinModulus.lean`, and do NOT commit.

Write:

`plan/GPT54_RESULT_37_BUILD_LOCAL_ROOT_BRANCH.md`
