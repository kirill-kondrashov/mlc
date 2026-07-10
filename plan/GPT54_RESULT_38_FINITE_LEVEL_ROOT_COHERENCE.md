# RESULT 38 — Finite-level coherence of local Böttcher root branches

## Summary

Landed corrected **Stage 2A** in a new leaf module:

- `Mlc/BottcherFiniteLevelCoherence.lean`

and registered it in `Mlc.lean` immediately after:

- `import Mlc.BottcherLocalRootBranch`

The new file adds:

- `LocalPullbackRootBranchData.lift_one_level`
- `localPullbackRootBranchData_of_iterate_outside_U_subset`
- `localPullbackRootBranchData_of_iterate_outside_lift_one_level`

This establishes **finite-level local compatibility**: if a Stage-1 local branch on level `N` stays inside the same escaping region on its neighborhood, then the same branch is automatically a valid local branch on level `N + 1` because

- `F_(N+1) = F_N^2`,
- so `g^(2^N) = F_N` implies `g^(2^(N+1)) = F_(N+1)`.

## What is now proved

The Stage-1 branch is canonically coherent across one finite escape-level step.
This is the correct next local compatibility statement before any genuine loop or monodromy comparison.

## What is **not** proved

This does **not** prove any of the following:

- global monodromy triviality on the basin;
- existence of a globally coherent basin value;
- `holo_on_basin`.

Those remain open.

## Rejected routes recorded by this task

The task explicitly rejected two invalid/too-strong targets:

1. **False simple-connectivity route**
   - Even in basic cases such as `c = 0`, the basin is an exterior domain in the plane, not a simply connected plane subset.
   - So a global logarithm / automatic monodromy kill from basin simple connectivity is not the right mechanism.

2. **Impossible all-level chart-chain target**
   - The existing all-level `BasinLoopChartChainMonodromyData` requirement is too strong as an immediate target.
   - At `c = 2`, basepoint `0`, level `N = 0`, the constant loop gives root-equation value `logSeriesBottcherApprox 2 0 = 0`, while the chart-chain setup requires zero-free charts, so that target is formally impossible there.

## Validation

Ran successfully:

- `lake build`
- `lake env lean check_axioms.lean`

Both passed with exit code `0`.

## Honest remaining seam

After Result 38, the Böttcher route has:

- unconditional basin preconnectedness;
- Stage 1 local root branches;
- Stage 2A finite-level local coherence.

Still missing are the genuinely global steps:

- loop/overlap compatibility beyond finite-level lifting,
- a coherent global basin value,
- discharge of `holo_on_basin`.
