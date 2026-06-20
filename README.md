# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/) *(GitHub Pages deploys from `main`; the checked-in `site/` directory reflects the current branch state.)*

A Lean 4 formalization of the Mandelbrot local connectivity statement
`MLC.mlc_conjecture`.

## Quick Start

```bash
make build
make check
make notebook
```

`make notebook` renders `notebooks/` to static HTML and serves the rendered
pages locally on
`127.0.0.1:8888`. This is a simple nbviewer-style workflow: load the rendered
notebook in a browser, rerender with `make notebook-render` after notebook
changes, and refresh the page manually. The uv project in `notebooks/`
contains the rendering dependencies. Override `NOTEBOOK_HOST`,
`NOTEBOOK_PORT`, `NOTEBOOK_DIR`, `NOTEBOOK_HTML_DIR`, or
`NOTEBOOK_PROJECT_DIR` if needed.

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

Current PLAN 09 work is to prove the vanishing-cocycle hypothesis for the
actual high-escaping curve. The abstract Čech-gluing reduction from cocycle
vanishing to closing equality is now formalized in Lean as
`Quadratic.logBranch_eqOn_closing_of_coboundary`.

The remaining theorem is therefore:

**Theorem (closing trivial monodromy).** Let

$$
U_0, \dots, U_m \subset \mathbf{C}^{\times}, \qquad
V_j \subset U_j \cap U_{j+1} \ \ (0 \le j < m), \qquad
V_{\mathrm{cl}} \subset U_m \cap U_0,
$$

$$
b_j : U_j \to \mathbf{C} \qquad (0 \le j \le m),
$$

Assume that

$$
A_K([t_j, t_{j+1}]) \subset U_j \qquad (0 \le j \le m),
$$

$$
b_{j+1}\vert_{V_j} = b_j\vert_{V_j} \qquad (0 \le j < m),
$$

and that all branches are obtained by analytic continuation of the same
normalized base germ. Then

$$
b_m\vert_{V_{\mathrm{cl}}} = b_0\vert_{V_{\mathrm{cl}}}.
$$

This is now reduced to proving that the associated logarithm-transition cocycle
class vanishes for the actual high-escaping chart cover:

$$
[c_{jk}] = 0 \in \check H^1(\Omega, 2\pi i \mathbf Z).
$$

`notebooks/plan09_actual_overlap_neighborhoods_companion.ipynb` now records the
closing theorem, the Čech-gluing reduction, a rigorous vanishing-cocycle
criterion, two positive numerical examples, a counterexample attempt showing
why the closing equality is necessary, and the one-domain special case.

`notebooks/frontier_plan09_vanishing_cocycle.ipynb` isolates the live PLAN 09
frontier: prove

$$
[c_{jk}] = 0 \in \check H^1(\Omega, 2\pi i \mathbf Z)
$$

for the actual high-escaping chart cover.

Once this theorem-level package exists,
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
   `notebooks/plan09_actual_overlap_neighborhoods_companion.ipynb`
   visualize the checked PLAN 08 / abstract PLAN 09 reduction, while
   `notebooks/frontier_plan09_vanishing_cocycle.ipynb` isolates the live
   cocycle-vanishing theorem, and
   `notebooks/archive/plan08_step13_actual_high_escaping_charts_frontier.ipynb`
   preserves the older Step 13 counterexample/status notebook.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
