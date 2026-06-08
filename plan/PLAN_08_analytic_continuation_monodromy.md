# PLAN 08: Analytic continuation and monodromy formalization

**Status:** PLANNED  
**Depends on:** `PLAN_07_monodromy_cover_route.md`

## Classification of the blocker

The remaining obstruction behind the basin extension is best classified as:

```text
mathematically known, formalization missing
```

The classical global Böttcher theorem is standard. What is missing in the
current Lean development is the analytic-topological infrastructure needed to
formalize coherent branch continuation on the basin of infinity.

## Immediate target

Construct an actual monodromy representation for basin loops:

```lean
PullbackRootMonodromyRepresentation
```

not for an abstract placeholder `Loop : Type`, but for a genuine formal type of
loops in the basin of infinity.

This should eventually supply:

```lean
MonodromyTrivialPullbackDataFor (2 : ℂ)
PrincipalPullbackCoherentDataFor (2 : ℂ)
ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

## Required formal components

### 1. Basin loop type

Define a usable formal loop type for the basin:

```lean
BasinLoop (c : ℂ) (z₀ : ℂ) : Type
```

Expected fields:

1. a continuous path `γ : Path z₀ z₀` or equivalent;
2. proof that the image of `γ` lies in `basin_of_infinity c`;
3. composition/reversal or a link to the existing fundamental-group machinery.

Goal:

```lean
BasinLoop.groupLike
```

or enough structure to define monodromy and prove invariance under homotopy.

### 2. Local root branch data

For each level `N` and local point `z₀`, define local branches solving

$$
w(z)^{2^N} =
\texttt{logSeriesBottcherApprox}\ c\ ((f_c)^{N}(z)).
$$

Needed surface:

```lean
LocalPullbackRootBranchData (c : ℂ) (N : ℕ) (z₀ : ℂ)
```

Expected fields:

1. neighborhood `U` of `z₀`;
2. holomorphic function `branch : U → ℂ`;
3. root equation on `U`;
4. compatibility with the near-infinity branch when `z₀` is already outside.

### 3. Analytic continuation along basin paths

Formalize continuation of `LocalPullbackRootBranchData` along a basin path.

Needed surface:

```lean
AnalyticContinuationAlongBasinPath
```

Expected output:

1. local branch at the endpoint;
2. proof that continuation preserves the root equation;
3. proof that two continuations along homotopic paths give the same monodromy
   element.

This is the largest missing analytic component.

### 4. Monodromy element

Given a loop and a starting branch, define the unique multiplier

$$
\rho_N(\gamma)\in\mu_{2^N}
$$

such that the continued branch equals

$$
\rho_N(\gamma)\cdot \text{(starting branch)}.
$$

Lean target:

```lean
actualPullbackRootMonodromy :
  BasinLoop c z₀ → rootsOfUnitySet (2^N)
```

Use the already checked torsor theorem:

```lean
pullbackRootSet_torsor_transitive
```

to prove uniqueness/existence of the multiplier once continuation is available.

### 5. Compatibility across levels

Prove:

```lean
actual_monodromy_compat :
  (ρ (N+1) γ)^2 = ρ N γ
```

This should use:

```lean
logSeries_pullbackRootSet_subset_next
```

and the squaring transition between root levels.

### 6. Trivial monodromy theorem

Prove the key classical fact:

```lean
actual_monodromy_trivial :
  ∀ N γ, ρ N γ = 1
```

Possible proof routes:

1. use basin topology and normalization near infinity to show all loops have
   zero effective winding for the normalized pullback branch;
2. use a monodromy theorem for analytic continuation of the already-normalized
   Böttcher coordinate;
3. prove a covering-space descent theorem for the monodromy-kernel cover.

### 7. Local chart proof template

The concrete proof strategy suggested by
`notebooks/plan08_missing_monodromy_theorem.ipynb` is:

1. **Push a basin loop to the `A`-plane.** For a basin loop `γ`, define

   $$
   A_N(t)=\Phi_\infty(f^N(\gamma(t))).
   $$

2. **Cover the image by zero-free simply connected charts.** Choose open sets
   `U_i ⊆ ℂ \ {0}` such that each `U_i` has a single logarithm branch and

   $$
   A_N([t_i,t_{i+1}])\subset U_i.
   $$

3. **Choose local roots.** On each chart define

   $$
   W_i(t)=\exp\left(\frac{1}{2^N}\mathrm{Log}_i(A_N(t))\right).
   $$

4. **Compare roots on overlaps.** On each overlap, prove the two local roots
   differ by a locally constant element

   $$
   \zeta_i\in\mu_{2^N}.
   $$

5. **Multiply overlap factors.** Define

   $$
   \rho_N(\gamma)=\prod_i \zeta_i.
   $$

   This is the monodromy element.

6. **Prove triviality.** Show

   $$
   \rho_N(\gamma)=1.
   $$

   Then the local branches glue to a single-valued branch along the loop.

The key local theorem surface has been implemented:

```lean
ZeroFreeChartRootBranchData
```

It packages:

1. a zero-free simply connected chart;
2. a logarithm branch on that chart;
3. the induced `2^N`-root branch;
4. proof that continuation inside the chart has trivial monodromy.

Current status of the local chart step: **implemented**. The same-chart trivial
monodromy constructors are:

```lean
AnalyticContinuationAlongBasinLoop.trivial
AnalyticContinuationAlongBasinLoop.trivial_multiplier
ZeroFreeChartRootBranchData.trivialContinuation
ZeroFreeChartRootBranchData.trivialContinuation_multiplier
```

The finite chart-chain product layer is also now implemented. The global
chart-chain declarations are:

```lean
BasinLoopChartCell
BasinLoopChartOverlapStep
BasinLoopChartChain
BasinLoopChartChain.monodromyProduct
BasinLoopChartChain.toOverlapRootMultiplierData
ChartChainContinuationData
BasinLoopChartChainMonodromyData
BasinLoopChartChainMonodromyData.toBasinLoopPullbackRootMonodromyData
BasinLoopChartChainMonodromyData.representation_trivial_of_products
```

Therefore neither the local zero-free-chart step nor the finite chain/product
bookkeeping is the current blocker. The conditional actual-data constructor is
also implemented:

```lean
puncturedPlaneZeroFreeChartRootBranchData
BasinLoopChartChain.of_nonzero_values
BasinLoopChartChain.monodromyProduct_of_nonzero_values
BasinLoopChartChainMonodromyData.of_nonzero_values_two
BasinLoopChartChainMonodromyData.of_nonzero_values_two_products
```

It constructs `BasinLoopChartChainMonodromyData (2 : ℂ) z₀` once the following
nonvanishing input is proved:

```lean
∀ (N : ℕ) (γ : BasinLoop (2 : ℂ) z₀) (t : ℝ),
  t ∈ Set.Icc (0 : ℝ) 1 →
    basinLoopRootEquationValue (2 : ℂ) N γ t ≠ 0
```

Thus the current blocker is no longer chart bookkeeping. It is the analytic
nonvanishing theorem above, or a replacement interface that only asks for
zero-free charts at sufficiently large escaping levels where
`one_lt_norm_logSeriesBottcherApprox_of_outside_open` applies.

The first option is now formally known to be false at the all-level interface:

```lean
logSeriesBottcherApprox_zero
not_forall_basinLoopRootEquationValue_ne_zero_two_zero
```

The escaping-level replacement has therefore been implemented:

```lean
BasinLoop.constant
BasinLoopLevelEscapes
basinLoopRootEquationValue_ne_zero_of_outside_open
basinLoopRootEquationValue_ne_zero_of_level_escapes
BasinLoopChartChain.of_escaping_level
BasinLoopChartChain.monodromyProduct_of_escaping_level
EscapingLevelBasinLoopChartChainMonodromyData
EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes
EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes_two
```

The algebraic descent and arbitrarily-high escaping-level layer from the
notebook have also been implemented:

```lean
BasinLoopLevelEscapes.mono
PullbackRootMonodromyRepresentation.monodromy_eq_one_of_add_eq_one
PullbackRootMonodromyRepresentation.monodromy_eq_one_of_le_of_top_eq_one
PullbackRootMonodromyRepresentation.trivial_of_arbitrarily_high_trivial
BasinLoopChartChainMonodromyData.representation_trivial_of_arbitrarily_high_products
ArbitrarilyHighEscapingLevelBasinLoopChartChainData
ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_eventual_level_escapes
EscapingLevelBasinLoopChartChainMonodromyData.toArbitrarilyHigh
BasinLoopChartChainMonodromyData.representation_trivial_of_high_escaping_comparison
```

The compactness/uniform-escape step from the notebook is also implemented:

```lean
BasinLoop.exists_levelEscapes
EscapingLevelBasinLoopChartChainMonodromyData.of_uniform_escape
EscapingLevelBasinLoopChartChainMonodromyData.of_uniform_escape_two
ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape
ArbitrarilyHighEscapingLevelBasinLoopChartChainData.of_uniform_escape_two
```

The current blocker is now narrower: the abstract overlap-equality comparison
argument is formalized, so the remaining task is to prove that the **actual**
high-level chart chains satisfy its hypotheses. Uniform escape and algebraic
descent from high-level triviality to all lower pullback levels are formalized.

The comparison endpoint, exact-chain special case, and uniform-escape
specialization have now been formalized:

```lean
HighEscapingChartChainProductComparisonData
HighEscapingChartChainProductComparisonData.of_chain_eq
HighEscapingChartChainProductComparisonData.representation_trivial
BasinLoopChartChainMonodromyData.representation_trivial_of_uniform_escape_comparison
```

The special case "local logs are restrictions of one global log branch" is now
formalized too:

```lean
ChartChainLocalLogsRestrictGlobal
ChartChainLocalLogsRestrictGlobal.overlap_multiplier_eq_one
ChartChainLocalLogsRestrictGlobal.monodromyProduct_eq_one
HighEscapingChartChainLocalLogsRestrictGlobalData
HighEscapingChartChainLocalLogsRestrictGlobalData.toProductComparisonData
```

The abstract overlap-equality theorem from the notebook's rigorous proof is now
formalized too:

```lean
ConnectedAnalyticZeroFreeChartRootBranchData
ConnectedAnalyticZeroFreeChartRootBranchData.logBranch_eqOn_of_eventuallyEq
ConnectedAnalyticZeroFreeChartRootBranchData.rootBranch_eq_of_eventuallyEq
BasinLoopChartOverlapStep.multiplier_eq_one_of_logBranch_eq
BasinLoopChartOverlapStep.multiplier_eq_one_of_eventuallyEq
ChartChainLocalLogsEventuallyEqAtOverlaps
ChartChainLocalLogsEventuallyEqAtOverlaps.monodromyProduct_eq_one
```

The generalized right-half-plane family from the notebook is formalized as:

```lean
complexRightHalfPlane
rightHalfPlaneZeroFreeChartRootBranchData
quadraticMap_two_second_iterate_eq
quadraticMap_two_second_iterate_re_lower_bound
quadraticMap_two_second_iterate_mem_rightHalfPlane_of_norm
```

The remaining comparison input is now even more specific: show that the actual
all-level chart chains at a sufficiently high escaping level supply the
overlap-neighborhood equality data required by
`ChartChainLocalLogsEventuallyEqAtOverlaps` (or a stronger global restriction
package implying it). Once that data is available, the monodromy product
comparison follows from the formalized overlap-equality theorem.

### 8. Produce existing seam

Once actual monodromy is built and proved trivial, fill:

```lean
MonodromyTrivialPullbackDataFor (2 : ℂ)
```

Then prove:

```lean
PrincipalPullbackCoherentDataFor (2 : ℂ)
```

or directly:

```lean
LogSeriesBasinExtensionDataFor (2 : ℂ)
```

## Recommended implementation order

1. **DONE:** define `BasinLoop`.
2. **DONE:** define `LocalPullbackRootBranchData`.
3. **DONE:** define `AnalyticContinuationAlongBasinLoop`.
4. **DONE:** define `BasinLoopPullbackRootMonodromyData`.
5. **DONE:** connect actual basin-loop monodromy data to
   `MonodromyTrivialPullbackDataFor` via
   `BasinLoopPullbackRootMonodromyData.toMonodromyTrivialPullbackDataFor`.
6. **DONE:** define `ZeroFreeChartRootBranchData`.
7. **DONE:** add the local chart theorem surface `ZeroFreeChartRootBranchData`.
8. **DONE:** prove the overlap multiplier theorem surface
   `overlap_root_multiplier_exists`.
9. **DONE:** add `OverlapRootMultiplierData` for the product of overlap
   multipliers around a loop.
10. **DONE:** prove the same-chart local trivial monodromy constructor:
   `AnalyticContinuationAlongBasinLoop.trivial`,
   `AnalyticContinuationAlongBasinLoop.trivial_multiplier`,
   `ZeroFreeChartRootBranchData.trivialContinuation`, and
   `ZeroFreeChartRootBranchData.trivialContinuation_multiplier`.
11. **DONE:** construct finite chart chains along basin loops and multiply the
   overlap multipliers via `BasinLoopChartChain.monodromyProduct`.
12. **BLOCKED / CONDITIONAL:** construct actual
   `BasinLoopChartChainMonodromyData` for `c = 2`. The conditional constructor
   `BasinLoopChartChainMonodromyData.of_nonzero_values_two` is implemented, and
   the all-level nonvanishing input is formally false at `z₀ = 0`. The
   escaping-level replacement
   `EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes_two` is
   implemented.
13. **PARTIAL DONE / NEXT:** the abstract overlap-equality comparison theorem is
   formalized. The remaining work is to construct, for the actual high
   escaping chart chains, the overlap-neighborhood equality data (or a
   stronger global chart package) needed to invoke
   `ChartChainLocalLogsEventuallyEqAtOverlaps.monodromyProduct_eq_one`, and
   then package the result as
   `HighEscapingChartChainProductComparisonData`.
14. **NEXT:** build `EscapeTimeIndependentPullbackDataFor (2 : ℂ)`.
15. **NEXT:** connect to `PrincipalPullbackCoherentDataFor`.

## Failure modes

If mathlib lacks enough covering/analytic-continuation infrastructure, the plan
should stop after adding exact theorem surfaces rather than adding axioms.

Do **not** replace this with random, principal, or nearest-root selection rules.
Those are diagnostics, not theorem-facing coherent branch constructions.
