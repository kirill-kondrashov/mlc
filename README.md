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

The current analytic route is to construct a genuine global Böttcher coordinate
at `c = 2` and use it to replace the remaining basin-external-ray axiom. The
near-infinity part is complete: the canonical coordinate is

```lean
MLC.logSeriesBottcherApprox c
```

packaged by:

```lean
Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox
Quadratic.genuineBottcherNearInfinityRouteFor_logSeriesBottcherApprox
```

The remaining work is basin extension. The current pullback candidate is:

```lean
Quadratic.principalPullbackLogSeriesBottcher
Quadratic.basinLogSeriesExtensionCandidate
```

The exact Route-A target is:

```lean
Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)
```

One field is checked: agreement with the near-infinity coordinate on the
canonical exterior.

```lean
Quadratic.basinLogSeriesExtensionCandidate_extends_near
```

The live obstruction is coherent pullback-root monodromy along basin loops.
PLAN 08 has reduced the Lean side to a precise analytic comparison input:

```lean
Quadratic.HighEscapingChartChainProductComparisonData
```

The finite chart-chain algebra is formalized:

```lean
Quadratic.BasinLoopChartChain
Quadratic.BasinLoopChartChain.monodromyProduct
Quadratic.BasinLoopChartChainMonodromyData
Quadratic.BasinLoopChartChainMonodromyData.toBasinLoopPullbackRootMonodromyData
```

Uniform escape over continuous basin loops and algebraic descent from high
escaping levels are formalized:

```lean
Quadratic.BasinLoop.exists_levelEscapes
Quadratic.ArbitrarilyHighEscapingLevelBasinLoopChartChainData
Quadratic.PullbackRootMonodromyRepresentation.trivial_of_arbitrarily_high_trivial
```

The special comparison case where local logarithm branches are restrictions of
one global logarithm branch is also formalized:

```lean
Quadratic.ChartChainLocalLogsRestrictGlobal
Quadratic.ChartChainLocalLogsRestrictGlobal.monodromyProduct_eq_one
Quadratic.HighEscapingChartChainLocalLogsRestrictGlobalData.toProductComparisonData
```

The generalized right-half-plane family from the notebook is checked:

```lean
Quadratic.rightHalfPlaneZeroFreeChartRootBranchData
Quadratic.quadraticMap_two_second_iterate_re_lower_bound
Quadratic.quadraticMap_two_second_iterate_mem_rightHalfPlane_of_norm
```

Current PLAN 09 work is the theorem/Lean instantiation for the actual
high-escaping curve:

1. choose the actual charts `U_j`,
2. choose the actual interior overlaps `V_j`,
3. choose the closing overlap `V_cl ⊂ U_m ∩ U_0`,
4. construct the actual logarithm branches `b_j` from the normalized base germ,
5. prove the interior and closing equalities needed by the cyclic monodromy
   comparison.

The one-global-log restriction package is a special case, not the general
Step 13 / PLAN 09 target.

The current notebook summary is:

- `notebooks/frontier_plan09_actual_overlap_neighborhoods.ipynb` lists the
  remaining mathematical point, the outstanding theorem, the Lean package to
  build, and the completion criterion for PLAN 09;
- the earlier numerical examples and counterexamples are kept in the related
  notebooks and git history.

Once that theorem-level package exists,
`HighEscapingChartChainProductComparisonData` should give trivial monodromy and
feed into `EscapeTimeIndependentPullbackDataFor (2 : ℂ)` and then
`PrincipalPullbackCoherentDataFor (2 : ℂ)`.

Current reduction seams:

```lean
Quadratic.LogSeriesBasinExtensionDataFor
Quadratic.PrincipalPullbackCoherentDataFor
Quadratic.LogSeriesExteriorInverseBasinExtensionDataFor
Quadratic.ClassicalGlobalExtensionFromNearInfinityDataFor
```

Checked reductions show that these basin-extension/global-extension packages are
enough to obtain `Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)`.

## Repository Snapshot

1. `make build`, `make check`, and `./scripts/verify_output.sh` pass.
2. `plan/PLAN_06_global_bottcher_package.md` records the current Böttcher plan.
3. `draft/` now records the single remaining positive mathematical target:
   `draft/genuine_bottcher_route_problem.md`.
4. `proof_sketches/` records the matching human-readable sketch:
   `proof_sketches/genuine_bottcher_route_proof.md`.
5. `plan/PLAN_08_analytic_continuation_monodromy.md` records the checked
   comparison layer, and `plan/PLAN_09_actual_overlap_neighborhoods.md` records
   the current geometric/theorem-level handoff.
6. `notebooks/plan08_chart_chain_monodromy_blocker.ipynb`,
   `notebooks/plan08_step13_overlap_comparison_frontier.ipynb`, and
   `notebooks/frontier_plan09_actual_overlap_neighborhoods.ipynb`
   visualize the live PLAN 08 / PLAN 09 frontier, while
   `notebooks/archive/plan08_step13_actual_high_escaping_charts_frontier.ipynb`
   preserves the older Step 13 counterexample/status notebook.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
