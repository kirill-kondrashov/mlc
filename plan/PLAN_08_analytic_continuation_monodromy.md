# PLAN 08: Analytic continuation and monodromy formalization

**Status:** ACTIVE — Step 13 abstract local proof formalized; actual `V_j` construction handed off to PLAN 09  
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

The current PLAN 08 task is no longer "construct the whole monodromy story from
scratch". The concrete loop type, local chart data, chart chains, escaping-level
replacement, abstract overlap-equality theorem, and the bridge from
open overlap equality to trivial monodromy are already formalized. In
particular, the abstract local implication is now checked through

```lean
ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn
```

What remains is to consume the output of

```text
PLAN_09_actual_overlap_neighborhoods.md
```

namely the overlap-neighborhood and branch-equality package for the
actual high-escaping chart chains, in order to build:

```lean
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
HighEscapingActualChartChainsProductComparisonData
```

for the **actual** high-escaping chart chains at `c = 2`.

Concretely, the geometric existence work for the actual charts `U_j`, overlap
neighborhoods `V_j`, and local branch equalities has been split out into
`PLAN_09_actual_overlap_neighborhoods.md`. PLAN 08 keeps the abstract
comparison theorem and the final packaging step: once PLAN 09 supplies those
chart data, the formalized comparison theorem gives trivial high-level
monodromy products.

The stronger special-case package

```lean
HighEscapingActualChartChainsLocalLogsRestrictGlobalData
```

is still useful, but only when the whole high-level loop image lies in one
zero-free global logarithm domain. The counterexample notebook
`notebooks/archive/plan08_step13_actual_high_escaping_charts_frontier.ipynb`
shows numerically that this fails for arbitrary basin loops, so it is no longer
the primary Step 13 target.

## Scope boundary

PLAN 08 is only the analytic-continuation / monodromy-comparison layer. It is
an input to the Böttcher route, but it is not the whole route.

The minimal dependency chain is:

1. PLAN 08 proves the actual high-level chart-chain comparison theorem.
2. This yields the monodromy-triviality ingredient for basin-loop pullback
   roots.
3. That ingredient is then combined with escape-time-independent pullback data
   and basin-extension arguments elsewhere.
4. Those downstream seams produce `PrincipalPullbackCoherentDataFor (2 : ℂ)`,
   `LogSeriesBasinExtensionDataFor (2 : ℂ)`, and then the checked Böttcher
   packages.

So the following objects are **downstream consumers / handoff targets**, not
independent PLAN 08 subgoals:

```lean
EscapeTimeIndependentPullbackDataFor (2 : ℂ)
MonodromyTrivialPullbackDataFor (2 : ℂ)
PrincipalPullbackCoherentDataFor (2 : ℂ)
ClassicalGlobalBottcherTheoremFor (2 : ℂ)
GenuineBottcherCoordinateDataFor (2 : ℂ)
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
`notebooks/plan09_actual_overlap_neighborhoods_companion.ipynb` is:

1. **Push a basin loop to the `A`-plane.** For a basin loop `γ`, define

   $$
   A_N(t)=\Phi_\infty(f^N(\gamma(t))).
   $$

2. **Cover the image by zero-free simply connected charts.** Choose open sets
   `U_i ⊆ ℂ \ {0}` such that each `U_i` has a single logarithm branch and

   $$
   A_N([t_i,t_{i+1}])\subset U_i.
   $$

3. **Choose normalized local logarithms.** On each chart choose a local
   logarithm branch `Log_i` obtained by continuation of the actual normalized
   starting germ. Do **not** assume in advance that there is one global
   logarithm branch on a neighborhood of the whole loop image.

4. **Choose local roots.** On each chart define

   $$
   W_i(t)=\exp\left(\frac{1}{2^N}\mathrm{Log}_i(A_N(t))\right).
   $$

5. **Compare roots on overlaps.** On each overlap, prove the two neighboring
   local roots differ by a locally constant element

   $$
   \zeta_i\in\mu_{2^N}.
   $$

   Equivalently, prove the local logarithm branches agree on a neighborhood of
   each overlap value, which is exactly the hypothesis consumed by
   `ChartChainLocalLogsEventuallyEqAtOverlaps`.

6. **Multiply overlap factors.** Define

   $$
   \rho_N(\gamma)=\prod_i \zeta_i.
   $$

   This is the monodromy element.

7. **Prove triviality.** Show

   $$
   \rho_N(\gamma)=1.
   $$

   Then the local branches glue coherently along the loop.

   This abstract implication is now formalized both through the eventual-equality
   API

   ```lean
   ChartChainLocalLogsEventuallyEqAtOverlaps.monodromyProduct_eq_one
   ```

   and directly from open overlap equalities via

   ```lean
   ChartChainLocalLogsEventuallyEqAtOverlaps.of_open_eqOn
   BasinLoopChartChain.monodromyProduct_eq_one_of_open_eqOn
   ```

The counterexample notebook also shows what this template must **not** require:
for general high-escaping loops, one cannot demand a single simply connected
zero-free neighborhood of the whole loop image carrying one global logarithm.
That stronger route survives only under an extra zero-winding / admissibility
hypothesis.

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
```

Indeed, the constant basin loop at `z₀ = 0` for `c = 2` gives a level-`0`
counterexample, since `basinLoopRootEquationValue (2 : ℂ) 0 γ 0 = 0`.

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
specialization have now been formalized. There are now two layers:
the high-level-only wrapper that does **not** assume an all-level chart-chain
monodromy package yet, and the older bridge form that applies once one is
available:

```lean
HighEscapingActualChartChainsProductComparisonData
HighEscapingActualChartChainsProductComparisonData.toAllLevelProductComparisonData
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
HighEscapingActualChartChainsLocalLogsRestrictGlobalData
HighEscapingActualChartChainsLocalLogsRestrictGlobalData.toProductComparisonData
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
HighEscapingActualChartChainsEventuallyEqAtOverlapsData
HighEscapingActualChartChainsEventuallyEqAtOverlapsData.toProductComparisonData
```

The generalized right-half-plane family from the notebook is formalized as:

```lean
complexRightHalfPlane
rightHalfPlaneZeroFreeChartRootBranchData
quadraticMap_two_second_iterate_eq
quadraticMap_two_second_iterate_re_lower_bound
quadraticMap_two_second_iterate_mem_rightHalfPlane_of_norm
```

The remaining comparison input is: show that the actual all-level chart chains
at a sufficiently high escaping level supply the overlap-neighborhood equality
data required by `ChartChainLocalLogsEventuallyEqAtOverlaps`. That existence
problem is tracked in `PLAN_09_actual_overlap_neighborhoods.md`. A stronger
global-restriction package still implies this, but only as a special case. Once
PLAN 09 produces the local overlap data, the monodromy product comparison
follows from the formalized overlap-equality theorem.

### 8. Downstream handoff after PLAN 08

Once the actual high-level comparison theorem is proved, the PLAN 08-specific
analytic continuation task is finished. What remains after that is a **handoff**
to the basin-extension package:

```lean
MonodromyTrivialPullbackDataFor (2 : ℂ)
PrincipalPullbackCoherentDataFor (2 : ℂ)
LogSeriesBasinExtensionDataFor (2 : ℂ)
```

These are still needed for the full Böttcher route, but they are not
separate monodromy-comparison subtasks. In particular, `EscapeTimeIndependentPullbackDataFor`
is an additional root-coherence input that must be combined with monodromy
triviality; it is not produced by the overlap-comparison theorem alone.

This handoff is now reflected by checked Lean theorem surfaces:

```lean
Quadratic.HighEscapingChartChainLocalLogsRestrictGlobalData.representation_trivial
Quadratic.HighEscapingChartChainLocalLogsRestrictGlobalData.toMonodromyTrivialPullbackDataFor
Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.representation_trivial
Quadratic.HighEscapingActualChartChainsLocalLogsRestrictGlobalData.toMonodromyTrivialPullbackDataFor
```

So the PLAN 08 output is no longer just an abstract comparison statement: the
global-log special case now lands directly at the `MonodromyTrivialPullbackDataFor`
handoff expected by PLAN 06 once escape-time-independent pullback values are
provided.

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
12. **BLOCKED IN ITS ORIGINAL FORM / REPLACED AT HIGH LEVELS:** construct
   actual `BasinLoopChartChainMonodromyData` for `c = 2`. The literal all-level
   constructor `BasinLoopChartChainMonodromyData.of_nonzero_values_two` is
   implemented, but its hypothesis is formally false at `z₀ = 0`. So this exact
   all-level route is not a live prerequisite anymore. The intended replacement
   interface at sufficiently high escaping levels,
   `EscapingLevelBasinLoopChartChainMonodromyData.of_level_escapes_two`, is
   implemented and is the route used by the later comparison steps.
13. **PARTIAL DONE / HANDED OFF:** the abstract overlap-equality comparison
   theorem and its open-set bridge to monodromy triviality are formalized.
   Starting from the escaping-level chain data from Step 12, the remaining
   geometric existence work has been split out to
   `PLAN_09_actual_overlap_neighborhoods.md`: construct, for the actual
   high-escaping chart chains, the overlap-neighborhood equality data needed
   to invoke those abstract theorems. PLAN 08 then packages the result first as
   `HighEscapingActualChartChainsEventuallyEqAtOverlapsData`. The stronger
   global-chart package
   `HighEscapingActualChartChainsLocalLogsRestrictGlobalData` survives only as a
   special-case route when the high-level image admits one global logarithm
   domain. Only after PLAN 09 supplies the actual domains, overlap
   neighborhoods, and logarithm/root branches for high-escaping loops
   should this be bridged to
   `HighEscapingChartChainProductComparisonData`.
14. **HANDOFF, NOT A NEW PLAN 08 BLOCKER:** combine the resulting monodromy
    triviality statement with an independently supplied
    `EscapeTimeIndependentPullbackDataFor (2 : ℂ)` to fill
    `MonodromyTrivialPullbackDataFor (2 : ℂ)`.
15. **HANDOFF TO PLAN 06 / BASIN EXTENSION PACKAGE:** use that seam to build
    `PrincipalPullbackCoherentDataFor (2 : ℂ)` (or another equivalent
    `LogSeriesBasinExtensionDataFor (2 : ℂ)` route) toward the checked
    Böttcher coordinate package.

## Failure modes

If mathlib lacks enough covering/analytic-continuation infrastructure, the plan
should stop after adding exact theorem surfaces rather than adding axioms.

Do **not** replace this with random, principal, or nearest-root selection rules.
Those are diagnostics, not coherent branch constructions.
