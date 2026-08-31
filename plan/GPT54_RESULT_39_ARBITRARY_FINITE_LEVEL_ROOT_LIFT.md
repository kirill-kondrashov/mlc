# RESULT 39 — Arbitrary finite-level lifting of local Böttcher branches

## Summary

Landed corrected **Stage 2B** in a new leaf module:

- `Mlc/BottcherArbitraryFiniteLevelLift.lean`

and registered it in `Mlc.lean` immediately after:

- `import Mlc.BottcherFiniteLevelCoherence`

The new file adds:

- `outside_iterate_add_of_outside`
- `exists_localPullbackRootBranchData_lift_levels`
- `localPullbackRootBranchData_of_iterate_outside_lift_levels`

This extends the previously landed one-step finite-level coherence to an
**arbitrary finite number of levels**. If the original level-`N` neighborhood is
in the outside-open region, forward invariance keeps all later iterates outside,
so the same local branch function can be reused at every finite level `N + d`.

## What is now proved

The Stage-1 local branch has a canonical arbitrary finite-level local lift.
Equivalently: for any finite `d`, there exists local branch data at level
`N + d` using the same neighborhood and the same branch function, provided the
initial neighborhood lies in the escaping region at level `N`.

## What is **not** proved

This does **not** prove:

- global loop comparison or overlap comparison for different local branches;
- existence of a coherent global basin value;
- global monodromy triviality;
- `holo_on_basin`.

All of those remain open.

## Validation

Ran successfully:

- `lake build`
- `lake env lean check_axioms.lean`

Both passed with exit code `0`.

## Honest remaining seam

After Result 39, the genuine Böttcher route has:

- unconditional basin preconnectedness;
- Stage 1 local root branches;
- Stage 2A one-step finite-level coherence;
- Stage 2B arbitrary finite-level local lifting.

Still missing are the genuinely global steps:

- compare local branches around loops / on overlaps,
- construct a single coherent basin value,
- discharge `holo_on_basin`.
