# PLAN 09: Actual overlap neighborhoods for high-escaping chart chains

**Status:** IN PROGRESS  
**Depends on:** `PLAN_08_analytic_continuation_monodromy.md`

## Goal

Construct the actual high-escaping chart/overlap data needed to build

```lean
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData
```

for the actual high-escaping chart chains at `c = 2`.

Equivalently, for a basin loop `γ` and sufficiently high escaping level `K`,
construct the finite family of actual charts

$$
(U_j, V_j, b_j, \xi_j)_{0 \le j \le m}
$$

such that:

1. each image segment of
   $$
   A_K(t) = \text{logSeriesBottcherApprox}\bigl(2, f_2^K(\gamma(t))\bigr)
   $$
   lies in `U_j`,
2. each adjacent overlap value `A_K(t_{j+1})` lies in an open neighborhood
   `V_j ⊂ U_j ∩ U_{j+1}`,
3. the actual neighboring logarithm branches agree on `V_j`.

PLAN 08 already proves that these data imply trivial overlap multipliers and a
trivial chart-chain monodromy product. Since the abstract Čech-gluing
implication is now formalized in Lean as
`Quadratic.logBranch_eqOn_closing_of_coboundary`, the live PLAN 09 frontier is
more precise: prove that the actual transition cocycle of the local logarithm
branches has vanishing class

$$
[c_{jk}] = 0 \in \check H^1(\Omega, 2\pi i \mathbf Z)
$$

for the actual high-escaping chart cover.

## Current formalized starting point

The following ingredients are already in Lean:

```lean
EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes_two
ChartChainLocalLogsEventuallyEqAtOverlaps
ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
HighEscapingActualChartChainsEventuallyEqAtOverlapsData.toProductComparisonData
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData.toOverlapNeighborhoodData
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData.toEventuallyEqAtOverlapsData
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData.toProductComparisonData
```

The remaining work is to construct the actual cover/branch data and prove the
vanishing-cocycle theorem that feeds these interfaces.

The notebook split is now:

1. `notebooks/plan09_actual_overlap_neighborhoods_companion.ipynb` for the
   closing theorem, the abstract Čech-gluing criterion, and the model cases;
2. `notebooks/frontier_plan09_vanishing_cocycle.ipynb` for the isolated live
   cocycle-vanishing frontier.

## Required components

### 1. High-level geometric cover of the actual image

For a basin loop `γ` and lower bound `N₀`, choose `K ≥ N₀` and a partition

$$
0 = t_0 < t_1 < \cdots < t_{m+1} = 1
$$

such that the actual high-level image `A_K([t_j,t_{j+1}])` sits inside a
zero-free simply connected chart `U_j`.

Needed outcome:

```lean
ActualHighEscapingChartCoverData
```

or an equivalent package producing the charts used by
`EscapingLevelBasinLoopChartChainMonodromyData`.

### 2. Actual overlap neighborhoods

For every adjacent pair `(U_j, U_{j+1})`, construct an open set

$$
V_j \subset U_j \cap U_{j+1}
$$

with

$$
A_K(t_{j+1}) \in V_j.
$$

PLAN 08 uses such `V_j`, but does not construct them.

Needed outcome:

```lean
ActualHighEscapingOverlapNeighborhoodData
```

or an equivalent package stating that each adjacent overlap value admits an
open overlap neighborhood inside both neighboring charts.

### 3. Actual local logarithm and root branches

On every actual chart `U_j`, define the genuine branches

$$
b_j : U_j \to \mathbf{C}, \qquad
\xi_j(w) = \exp\!\left(\frac{1}{2^K} b_j(w)\right),
$$

obtained by continuation of the normalized near-infinity germ.

Needed outcome:

```lean
ActualHighEscapingLocalBranchData
```

or a package that records the actual branches attached to the chosen
charts.

### 4. Equality of actual neighboring branches on `V_j`

Prove for every adjacent pair that

$$
b_{j+1} = b_j \quad \text{on } V_j.
$$

Equivalently,

$$
\xi_{j+1} = \xi_j \quad \text{on } V_j.
$$

This is the remaining hypothesis required by

```lean
ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
```

and therefore by

```lean
BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn.
```

### 5. Vanishing of the transition cocycle

For all overlaps of the actual chart cover, define

$$
c_{jk} = b_k - b_j \in 2\pi i \mathbf Z.
$$

The live theorem is to prove that this cocycle is a coboundary:

$$
[c_{jk}] = 0 \in \check H^1(\Omega, 2\pi i \mathbf Z).
$$

Equivalently, one must construct constants $a_j \in 2\pi i \mathbf Z$ such
that

$$
c_{jk} = a_k - a_j
$$

on the relevant overlaps.

### 6. Packaging into the PLAN 08 interface

Assemble the chart, overlap, and branch-equality data into

```lean
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData
```

and then derive

```lean
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
HighEscapingActualChartChainsProductComparisonData.
```

This is the exact output consumed back in PLAN 08.

## Suggested proof strategy

1. Use sufficiently high escaping estimates to force the actual image into a
   region where local logarithm charts can be chosen uniformly.
2. Refine the parameter partition until each image segment lies in one
   zero-free simply connected chart and each adjacent overlap value lies in a
   smaller open set contained in both neighboring charts.
3. Define the actual branches by continuation from the normalized starting germ.
4. Use uniqueness of analytic continuation / identity-theorem arguments to show
   the adjacent branches coincide on the overlap neighborhoods.
5. Prove that the resulting transition cocycle on the finite overlap nerve is
   cohomologically trivial.
6. Package the resulting data into the existing PLAN 08 interfaces.

## Scope boundary

This plan should not reprove abstract monodromy triviality, add a new global
logarithm theorem, or replace the local theorem by a special-case global-domain
package.

Its purpose is:

- construct the actual `V_j`,
- construct the local branches on the actual charts,
- prove equality on those `V_j`,
- prove vanishing of the induced transition cocycle,
- feed the result back into PLAN 08.

## Deliverable

The deliverable of this plan is a checked constructor or theorem package giving

```lean
HighEscapingActualChartChainsEqOnOverlapNeighborhoodData
```

for the actual high-escaping chart chains at `c = 2`, together with the induced
eventual-equality and product-comparison data used by PLAN 08.

In the global-log special case tracked by the frontier notebook, the checked
handoff now continues through

```lean
HighEscapingActualChartChainsLocalLogsRestrictGlobalData.representation_trivial
HighEscapingActualChartChainsLocalLogsRestrictGlobalData.toMonodromyTrivialPullbackDataFor
```

so the PLAN 09 theorem-level target is now aligned with the genuine-route
rewiring in PLAN 06 rather than only with the older proxy-root comparison
surface.
