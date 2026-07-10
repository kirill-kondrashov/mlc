# RESULT 37 — Build local holomorphic root branches (Stage 1)

Task 37 is complete.

## What landed

Created the new leaf file:

- `Mlc/BottcherLocalRootBranch.lean`

and registered it from `Mlc.lean` immediately after `import Mlc.BasinConnected`:

- `import Mlc.BottcherLocalRootBranch`

The file adds exactly the requested declarations:

- `differentiable_quadratic_iterate`
- `mem_basin_of_iterate_mem_basin`
- `localPullbackRootBranchData_of_iterate_outside`

## What is now available

Stage 1 of the coherent Böttcher-route repair is now landed.

Precisely, for any parameter `c`, iterate level `N`, center `z₀`, and escape
hypothesis

- `‖(MLC.quadratic_map c)^[N] z₀‖ > ‖c‖ + 2`,

we now have

- `localPullbackRootBranchData_of_iterate_outside c N z₀ hz₀ : LocalPullbackRootBranchData c N z₀`.

So near any point whose `N`-th iterate has escaped the trapping disk, the codebase
now produces a local holomorphic `2^N`-th-root branch of the pulled-back
near-infinity coordinate, packaged in the existing `LocalPullbackRootBranchData`
structure.

The branch is built on a neighborhood where the ratio
`F z / F z₀` stays in the right-half disk `‖· - 1‖ < 1 ⊆ slitPlane`, so
`Complex.log` is used on a genuine local slit-avoiding domain rather than via the
broken global principal branch.

## Validation

Passed:

- `lake build` → success (`7979` jobs)
- `lake env lean check_axioms.lean` → exit code `0`

Final build tail:

```text
✔ [7978/7979] Built Mlc (4.7s)
Build completed successfully (7979 jobs).
```

Axiom check status:

```text
exit code 0
```

## `sorry` / `axiom` status

No new `sorry`, `admit`, or declaration-level `axiom` was introduced.

The axiom frontier remains unchanged: exactly the two project axioms (plus the
already-allowed standard logical / classical axioms tracked by
`check_axioms.lean`).

## What this does NOT do

This does **not** repair the discontinuous literal candidate
`basinLogSeriesExtensionCandidate`; that candidate remains wrong because the
principal-`cpow` branch cut creates genuine discontinuity.

It also does **not** discharge `holo_on_basin` yet.

What is finished here is only **Stage 1**:
- local holomorphic root branches.

Still remaining:
- **Stage 2:** construct a globally coherent value via monodromy triviality /
  simple-connectivity on the basin;
- **Stage 3:** assemble those local branches into the coherent holomorphic basin
  coordinate and discharge `holo_on_basin`.

And even after all three stages are finished, that closes only the Böttcher-route
holomorphicity residual. Beyond that, the parameter-plane axiom still has three
further Yoccoz-scale pieces remaining (holomorphic inverse `Φ_c⁻¹`,
puzzle-boundary holomorphic motion, and parameter↔dynamical correspondence).

## Scope discipline

As requested:

- `ConstructiveBasinCoordinate.lean` was untouched;
- `ConstructiveBasinModulus.lean` was untouched;
- no other existing file was edited except the one import line in `Mlc.lean`;
- no commit was made.
