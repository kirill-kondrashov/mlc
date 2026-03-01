# PLAN 06: New Proof Architecture — Bypass the False.elim Chain

**Status:** `██░░░░░░░░░░░░░░░░░░` **10%**
**State:** `BLOCKED` — all routes have same fundamental gaps (FR connectivity
or IR classification)
**Difficulty:** Medium-High
**Risk:** Medium — restructures the proof without changing `bottcher_map`.

## Core Idea

Keep the crude `bottcher_map` but **remove the entire vacuous proof chain**
(BottcherSurjOnExterior → approach-to-1 → False → MainPathData → MLC).
Replace it with a proof architecture that routes `mlc_conjecture` through
components that CAN be proved without axioms.

## The Current Architecture (Broken)

```
external_ray_map_exists (AXIOM, provably false at c=2)
  → ExternalRayMapData (2)
  → BottcherSurjOnExterior (2)  [FALSE for crude map]
  → BottcherApproachOneSeqFiberData (2)
  → BottcherApproachToOneSeqPreimageData (2) [FALSE — proved in lemma]
  → False
  → MainPathData
  → mlc_strategy_of_branchLocalData
  → LocallyConnectedSpace mandelbrotSet
```

## Proposed Architecture Options

### Option A: Direct to `mlc_strategy_of_branchLocalData`

```
PuzzleBoundaryMotionHyp (from Yoccoz puzzle shrinking)
+ IRClassificationData (from combinatorial classification)
+ Molecule bridge
  → mlc_strategy_of_branchLocalData
  → LocallyConnectedSpace mandelbrotSet
```

This is Plan 02. Requires proving the three major components.

### Option B: Parametric approach via Green function

For every c in M, the Mandelbrot set is locally connected at c iff the
intersection of para-puzzle pieces shrinks to {c}. This is formalized in
`parameter_shrink_of_yoccoz`:

```lean
theorem parameter_shrink_of_yoccoz :
    ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (_h : FinitelyRenormalizable c),
      (⋂ n, DynamicalPuzzlePiece c n 0) = {0} →
      (⋂ n, ParaPuzzlePieceAt c n) = {c}
```

If we can prove `(⋂ n, DynamicalPuzzlePiece c n 0) = {0}` for all c ∈ M,
we get local connectivity at all finitely renormalizable parameters.

The dynamical puzzle piece intersection equals {0} iff the Green function
provides enough separation — this is a statement about the Green function,
NOT about the Böttcher coordinate.

### Option C: Level-set topology approach

Local connectivity of M is equivalent to:
- The complement ℂ\M is connected, AND
- M is the intersection of a nested sequence of locally connected compact sets

The complement ℂ\M is connected (Douady-Hubbard, uses the Böttcher map of
the MANDELBROT set, not of individual Julia sets). This is a different
Böttcher coordinate: Φ : ℂ\M → {|w| > 1} is the uniformization of the
complement of the Mandelbrot set. It's defined by Φ(c) = φ_c(c) where φ_c
is the Böttcher coordinate of the polynomial z² + c.

MLC is equivalent to Φ extending continuously to ∂M.

This gives a different approach: prove that parameter external rays land.

### Option D: Combine existing valid components

Looking at what's already proved WITHOUT the axiom:

- `dichotomy`: every c is finitely or infinitely renormalizable ✓
- `parameter_shrink_of_yoccoz`: puzzle shrinking bridge ✓
- Various puzzle piece connectivity results ✓
- Green function properties ✓
- Escape bounds ✓

What's MISSING (only obtained via False.elim):
- `PuzzleBoundaryMotionHyp`
- `IRClassificationData` 
- `IRNoTowerPrimitiveAndMoleculeBridgeTargetData`

**Focus:** which of these missing components can be proved most easily?

**Audit results (2026-03-01):**

| Component | Difficulty | Notes |
|-----------|-----------|-------|
| `PuzzleBoundaryMotionHyp` | Very High | Requires holomorphic motion formalization |
| `para_puzzle_piece_inter_mandelbrot_connected` | High | Currently axiom; proving it requires M ∩ puzzle piece connectivity |
| `IRClassificationData` | High | Combinatorial, but deep renormalization theory |
| `lyubich_conformal_bridge` | High | Currently axiom; bridges placeholder to real modulus |
| `MoleculeConjectureRefined` | Very High | Dudko-Lyubich renormalization |

**Nearest unblocking target:** proving `para_puzzle_piece_inter_mandelbrot_connected`
(FR connectivity). This would close the FR branch given that `yoccoz_theorem`,
`parameter_shrink_of_yoccoz`, and `lc_at_of_shrink_of_connected_at` are all proved.

### Option E: Prove a special case of MLC

MLC for real parameters (c ∈ [-2, 1/4]) is significantly easier.
The proof uses one-dimensional real analysis: Lyubich's theorem that the
Mandelbrot set restricted to the real line is the interval [-2, 1/4].

This wouldn't prove full MLC but might establish a simpler target that
breaks the dependency on the axiom.

## Recommended Path

**Option D** — audit exactly what's missing and whether any of the three
major components can be proved from existing infrastructure.

### Audit Steps

1. **Trace `PuzzleBoundaryMotionHyp`**: what does it actually state? Is it
   close to something provable from the Yoccoz library?

2. **Trace `IRClassificationData`**: is this a deep theorem or just a
   dichotomy (excluded middle on some property)?

3. **Trace the molecule bridge**: what is `MoleculeConjectureRefined`? Is it
   assumed or proved?

4. For each, determine:
   - Is it purely combinatorial (provable in Lean)?
   - Does it require analytic content (needs new formalization)?
   - Is it equivalent to a known result already in the codebase?

## Implementation Skeleton

```lean
-- New root theorem, bypassing the Böttcher chain:
theorem mlc_conjecture_direct :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin | h_inf
  · exact finite_branch_lc c hc h_fin  -- Yoccoz puzzle
  · exact infinite_branch_lc c hc h_inf  -- IR classification + bridge
```

Where `finite_branch_lc` and `infinite_branch_lc` are new theorems that
don't go through the Böttcher map.
