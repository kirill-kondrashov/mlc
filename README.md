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

One non-core project axiom remains: `MLC.basinExternalRayKernelTwo`.

The current analytic target is:

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

The genuine canonical near-infinity coordinate is already constructed as:

```lean
MLC.logSeriesBottcherApprox c
```

and packaged by:

```lean
Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox
Quadratic.genuineBottcherNearInfinityRouteFor_logSeriesBottcherApprox
```

The remaining blocker is basin extension. The current principal pullback
candidate is:

```lean
Quadratic.principalPullbackLogSeriesBottcher
Quadratic.basinLogSeriesExtensionCandidate
```

The exact Route-A target is:

```lean
Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)
```

One field is checked:
`Quadratic.basinLogSeriesExtensionCandidate_extends_near`, agreement with the
near-infinity coordinate on the canonical exterior. The open fields are
coherent branch independence, basin exterior-valuedness, basin characterization,
basin semiconjugacy, basin differentiability, Green-function modulus, and
normalization of the total basin extension.

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
2. `plan/PLAN_06_global_bottcher_package.md` records the live theorem-facing
   Böttcher plan.
3. `draft/` now records the single remaining positive mathematical target:
   `draft/genuine_bottcher_route_problem.md`.
4. `proof_sketches/` records the matching human-readable sketch:
   `proof_sketches/genuine_bottcher_route_proof.md`.
5. The genuine near-infinity Böttcher coordinate is checked; the remaining work
   is the basin extension and inverse package.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
