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

The key local theorem surface should be:

```lean
ZeroFreeChartRootBranchData
```

with fields:

1. a zero-free simply connected chart;
2. a logarithm branch on that chart;
3. the induced `2^N`-root branch;
4. proof that continuation inside the chart has trivial monodromy.

Then the global basin-loop theorem should be built by chaining such charts along
the loop and multiplying the overlap root-of-unity factors.

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
6. **NEXT:** define `ZeroFreeChartRootBranchData`.
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
11. **NEXT:** construct actual chart chains along basin loops and multiply the
   overlap multipliers.
12. **NEXT:** construct actual `BasinLoopPullbackRootMonodromyData` for
   `c = 2`.
13. **NEXT:** prove its monodromy is trivial.
14. **NEXT:** build `EscapeTimeIndependentPullbackDataFor (2 : ℂ)`.
15. **NEXT:** connect to `PrincipalPullbackCoherentDataFor`.

## Failure modes

If mathlib lacks enough covering/analytic-continuation infrastructure, the plan
should stop after adding exact theorem surfaces rather than adding axioms.

Do **not** replace this with random, principal, or nearest-root selection rules.
Those are diagnostics, not theorem-facing coherent branch constructions.
