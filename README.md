# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/) *(GitHub Pages deploys from `main`; the checked-in `site/` directory reflects the current branch state.)*

A Lean 4 formalization of the Mandelbrot local connectivity statement
`MLC.mlc_conjecture`.

## Quick Start

```bash
make build
make check
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.basinExternalRayKernelTwo
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.basinExternalRayKernelTwo}

project_frontier(MLC.mlc_conjecture)
= {MLC.basinExternalRayKernelTwo}
```

## Current Status

The checked root still has a single non-core project assumption,
`MLC.basinExternalRayKernelTwo`, but the Böttcher-coordinate side has advanced
substantially.

The old proxy coordinate `Quadratic.proxy_bottcher_map := polar_green_map` is not
the theorem-facing coordinate. The current genuine near-infinity coordinate is
the logarithmic-series coordinate

```lean
MLC.logSeriesBottcherApprox c
```

and the canonical near-infinity package is now checked:

```lean
Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox
Quadratic.genuineBottcherNearInfinityRouteFor_logSeriesBottcherApprox
```

This gives exterior-valuedness, conjugacy to squaring, differentiability on the
canonical outside-open region, and normalization at infinity for the genuine
coordinate, without adding axioms.

## Remaining Blocker

One non-core project axiom remains:

1. `MLC.basinExternalRayKernelTwo`

It is the theorem-shaped scope interface
`BasinExternalRayMapDataTwoMinimalCounterexample`, whose positive content is the
specialized basin-valued inverse package `Quadratic.BasinExternalRayMapDataTwo`.

So there is only **one** root-facing missing theorem in the checked proof. The
current analytic blocker behind it is no longer the near-infinity construction:
it is extending `logSeriesBottcherApprox` from the canonical outside-open region
to the full basin of infinity.

The principal pullback candidate is formalized:

```lean
Quadratic.principalPullbackLogSeriesBottcher
Quadratic.basinLogSeriesExtensionCandidate
```

and the exact remaining coherent-pullback target is isolated as:

```lean
Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)
```

One field is already checked:
`basinLogSeriesExtensionCandidate_extends_near`, agreement with the
near-infinity coordinate on the canonical exterior. The remaining fields are
basin exterior-valuedness, basin characterization by exterior norm, basin
semiconjugacy, differentiability on the basin, Green-function modulus, and
normalization of the total extension.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Remaining Mathematical Target

The immediate target is:

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

Current reduction seams:

```lean
Quadratic.LogSeriesBasinExtensionDataFor
Quadratic.PrincipalPullbackCoherentDataFor
Quadratic.LogSeriesExteriorInverseBasinExtensionDataFor
Quadratic.ClassicalGlobalExtensionFromNearInfinityDataFor
```

Checked reductions show that any of these basin-extension/global-extension data
packages is enough to obtain the classical global Böttcher theorem. The next
exact target is therefore:

```lean
Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)
```

## Repository Snapshot

1. `make build`, `make check`, and `./scripts/verify_output.sh` pass.
2. `plan/` records the live theorem-facing Böttcher plan in
   `PLAN_06_global_bottcher_package.md`, alongside completed or auxiliary
   historical plans.
3. `draft/` now records the single remaining positive mathematical target:
   `draft/genuine_bottcher_route_problem.md`.
4. `proof_sketches/` records the matching human-readable sketch:
   `proof_sketches/genuine_bottcher_route_proof.md`.
5. The current root-facing story is therefore honest: one residual
   theorem-facing assumption remains, the genuine near-infinity Böttcher
   coordinate is checked, and the remaining work is the basin extension and
   inverse package.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
