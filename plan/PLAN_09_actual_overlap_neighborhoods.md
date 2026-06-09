# PLAN 09: Actual overlap neighborhoods for high-escaping chart chains

**Status:** PLANNED  
**Depends on:** `PLAN_08_analytic_continuation_monodromy.md`

## Goal

Construct the genuine local overlap data needed to instantiate

```lean
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
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

PLAN 08 already proves that once these data exist, the overlap multipliers and
the chart-chain monodromy product are trivial. So this plan isolates the
remaining geometric/analytic existence work.

## Current formalized starting point

The following ingredients are already in Lean:

```lean
EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes_two
ChartChainLocalLogsEventuallyEqAtOverlaps
ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
HighEscapingActualChartChainsEventuallyEqAtOverlapsData.toProductComparisonData
```

So the missing issue is **not** a new monodromy theorem. The missing issue is to
construct the actual open sets and actual branch-equality data that feed those
interfaces.

The frontier notebook
`notebooks/frontier_plan09_actual_overlap_neighborhoods.ipynb`
already records the right target:

- the discarded universal global-log package is false in general;
- the weakened local chart-chain theorem is the correct statement;
- no numerical counterexample is currently known to that weakened theorem;
- the missing proof is the existence of the genuine `V_j` and the equality of
  actual adjacent branches on them.

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

or an equivalent theorem surface producing the charts used by
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

This is the exact point of the handoff: PLAN 08 consumes such `V_j`, but does
not currently produce them.

Needed outcome:

```lean
ActualHighEscapingOverlapNeighborhoodData
```

or an equivalent package stating that every adjacent overlap value admits an
actual open overlap neighborhood inside both neighboring charts.

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

or a theorem surface that packages the actual branches attached to the chosen
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

This is the final missing hypothesis required by

```lean
ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
```

and therefore by

```lean
BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn.
```

### 5. Packaging into the PLAN 08 interface

Assemble the chart, overlap, and branch-equality data into

```lean
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
```

and then derive

```lean
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
5. Package the resulting data into the existing PLAN 08 theorem surface.

## Scope boundary

This plan should **not** try to reprove abstract monodromy triviality, invent a
new global logarithm theorem, or replace the local theorem by a special-case
global-domain package.

Its purpose is narrower:

- construct the genuine `V_j`,
- construct the genuine local branches on the actual charts,
- prove equality on those `V_j`,
- feed the result back into PLAN 08.

## Deliverable

The deliverable of this plan is a checked constructor or theorem package giving

```lean
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
```

for the actual high-escaping chart chains at `c = 2`, together with the induced
product-comparison data used by PLAN 08.
