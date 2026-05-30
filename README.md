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
- MLC.restrictedWindingKernelTwo
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.restrictedWindingKernelTwo}

project_frontier(MLC.mlc_conjecture)
= {MLC.restrictedWindingKernelTwo}
```

## Current Status

The checked root is now routed through a **single residual degree-one kernel**:
a classical scope gate for the direct proper/local witness on the restricted
outside map together with the exact generator calculation from the proof sketch.
Lean already formalizes the positive constant covering degree and the large-circle
free homotopy, so the remaining topology seam is now the monodromy /
fundamental-group step reducing that degree to `1`. The coordinate-data and
normalization pieces are constructive again, and the root still avoids the older
tower / Lyubich / Problem 4.5 detours.

1. `mlc_conjecture_of_finalAxiomCoreConstructiveGapV16`
2. `finalAxiomCoreConstructiveGapV16_of_restricted_winding`
3. the root kernel `MLC.restrictedWindingKernelTwo`

So the earlier explicit frontier

1. para-puzzle connectedness,
2. residual virtual near-Molecule data,
3. chosen-true primitive bridge data,
4. bounded-type primitive Feigenbaum inputs,

has been pushed off the checked root. Those routes still exist in the repo, but
they are no longer part of `Axioms(MLC.mlc_conjecture)`.

## Remaining Blocker

One non-core project axiom remains:

1. `MLC.restrictedWindingKernelTwo`

This kernel is the conjunction of:

1. `DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwoScope`
2. `Mlc.Bottcher.DegreeOne.RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo`

The theorem-facing coordinate and root normalization branches are now supplied
constructively by the explicit `polar_green_map` / basin-valued Böttcher package.

## Non-solutions

The repository still rejects reroutes that revive older project axioms, notably
through:

1. `ir_locally_connected_seam`
2. `InconsistencyRoute` / `lyubich_conformal_bridge`
3. renormalization-tower existence bridge axioms

## Elimination Target

The final constructive target is now the exact `c = 2` degree-one kernel:
construct the local-homeomorph/closed-preimage route to the direct proper/local
witness for the restricted outside map and prove the remaining generator calculation
`Mlc.Bottcher.DegreeOne.RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo`.
The witness half is no longer a raw scope gate for `DirectProperLocalWitnessTwo`;
it is now a scope gate for the more explicit route
`DirectProperLocalWitnessTwoFromLocalHomeomorphClosedRangeRouteTwo`, from which
the direct witness is derived constructively. The topology target is stated in
the already-formalized proper/local covering context, so it is no longer a bare
continuous-map claim. From that theorem Lean already derives the coarser annulus
statement `RestrictedAnnulusCoveringDegreeOneStepTwo`, and then the large-circle
homotopy bridge closes the degree-one route. Doing so will eliminate the last
root axiom `MLC.restrictedWindingKernelTwo`.

## Repository Snapshot

1. `make build`, `make check`, and `./scripts/verify_output.sh` pass.
2. `plan/` has been pruned to the single live frontier file
   `PLAN_04_lyubich_bridge.md`.
3. The current root-facing story is therefore simple: one remaining mathematical
   elimination target, exposed as one residual theorem-facing assumption.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
