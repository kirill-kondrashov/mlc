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
- MLC.residualOpenVirtualNearMoleculeAxiom
- MLC.unifiedGenuineRootKernelTwo
```

## Current Frontier

```text
Axioms(MLC.mlc_conjecture)
= {Quot.sound, propext, Classical.choice,
   MLC.residualOpenVirtualNearMoleculeAxiom,
   MLC.unifiedGenuineRootKernelTwo}

project_frontier(MLC.mlc_conjecture)
= {MLC.residualOpenVirtualNearMoleculeAxiom,
   MLC.unifiedGenuineRootKernelTwo}
```

## Current Status

Two non-core project axioms remain:
`MLC.residualOpenVirtualNearMoleculeAxiom` and
`MLC.unifiedGenuineRootKernelTwo`.

They are now understood to be two independent frontier axes:

1. `MLC.unifiedGenuineRootKernelTwo` is the active PLAN 06/08/09 analytic
   Böttcher-coordinate program.
2. `MLC.residualOpenVirtualNearMoleculeAxiom` is the renormalization-theory
   seam packaging exactly Dudko Problem 4.3 (pseudo-Siegel a priori bounds in
   the remaining unbounded satellite `ql` cases) and Problem 4.4 (the Virtual
   Molecule near-degenerate interpolation regime).

As of the Dec 2025 literature snapshot in `refs/2512.24171v1.txt`, Problems
4.3 and 4.4 remain open. In the current repository, the Gaussian proxy modulus
framework also cannot honestly prove the Track-2 side: see
`Mlc/MoleculeGroetzschConnection.lean`, where the proxy makes the relevant
conformal-modulus non-summability target false. So PLAN 06/08/09 can eliminate
only `MLC.unifiedGenuineRootKernelTwo`; it does not attack
`MLC.residualOpenVirtualNearMoleculeAxiom`.

The current analytic route is to construct a genuine global Böttcher coordinate
at `c = 2` and use it to replace the remaining unified genuine-route kernel. The
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
Quadratic.HighEscapingChartChainLocalLogsRestrictGlobalData.representation_trivial
Quadratic.HighEscapingChartChainLocalLogsRestrictGlobalData.toMonodromyTrivialPullbackDataFor
Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.representation_trivial
Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.toMonodromyTrivialPullbackDataFor
```

The generalized right-half-plane family from the notebook is checked:

```lean
Quadratic.rightHalfPlaneZeroFreeChartRootBranchData
Quadratic.quadraticMap_two_second_iterate_re_lower_bound
Quadratic.quadraticMap_two_second_iterate_mem_rightHalfPlane_of_norm
```

Current PLAN 09 work on the actual high-escaping cover is now split cleanly in
Lean. The notebook's anchored-global-log reduction from the `Exact rigorous
proof status` section is formalized as
`Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.actualChain_monodromyProduct_eq_one`,
`Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.representation_trivial`,
and
`Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.toMonodromyTrivialPullbackDataFor`.
The remaining gap is to prove the anchored global-log / vanishing-cocycle
hypothesis for the actual high-escaping cover itself. The abstract Čech-gluing
reduction from cocycle vanishing to closing equality is formalized separately as
`Quadratic.logBranch_eqOn_closing_of_coboundary`.

The root-facing genuine-route cutover is now also exposed explicitly:

```lean
MLC.MainProof.mlc_conjecture_of_principalPullbackCoherentData_two
MLC.MainProof.mlc_conjecture_of_unifiedGlobalBottcherTheorem_two
```

These theorems rewire the final entrypoint away from the old
proxy-specific basin-external-ray route: once
`Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)` and the matching inverse
package for `Quadratic.basinLogSeriesExtensionCandidate (2 : ℂ)` are available,
or more directly once `Quadratic.UnifiedGlobalBottcherTheoremFor (2 : ℂ)` is
available, the existing genuine Böttcher chain closes MLC through the current
`bottcher_onM_hyp` motion stub. The separate theorem-facing motion-bridge
conjunct is no longer part of the live analytic frontier.

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

This is now reduced to proving enough anchored global-log data, equivalently the
vanishing of the associated logarithm-transition cocycle class for the actual
high-escaping chart cover:

$$
[c_{jk}] = 0 \in \check H^1(\Omega, 2\pi i \mathbf Z).
$$

`notebooks/plan09_actual_overlap_neighborhoods_companion.ipynb` now records the
closing theorem, the Čech-gluing reduction, a rigorous vanishing-cocycle
criterion, two positive numerical examples, a counterexample attempt showing
why the closing equality is necessary, and the one-domain special case.

`notebooks/plan09_vanishing_cocycle_companion.ipynb` now records the PLAN 09
cocycle-vanishing layer: prove

$$
[c_{jk}] = 0 \in \check H^1(\Omega, 2\pi i \mathbf Z)
$$

for the actual high-escaping chart cover.

The single live frontier notebook is now
`notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb`, which
isolates the single strongest missing global Bottcher theorem behind the genuine
cutover. Its companion notebook
`notebooks/plan06_principal_pullback_coherence_companion.ipynb` unpacks that
frontier into the theorem surfaces
`Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)` and the matching inverse
package.

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
   `notebooks/plan08_step13_overlap_comparison_companion.ipynb`,
   `notebooks/plan09_actual_overlap_neighborhoods_companion.ipynb`, and
   `notebooks/plan09_vanishing_cocycle_companion.ipynb`
   visualize the checked PLAN 08 / PLAN 09 reduction, while
   `notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb` isolates
   the live unified frontier, while
   `notebooks/plan06_principal_pullback_coherence_companion.ipynb` keeps the
   PLAN 06 companion unpacking, and
   `notebooks/archive/plan08_step13_actual_high_escaping_charts_frontier.ipynb`
   preserves the older Step 13 counterexample/status notebook.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
