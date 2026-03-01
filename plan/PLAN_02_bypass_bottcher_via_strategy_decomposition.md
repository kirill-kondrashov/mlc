# PLAN 02: Bypass Böttcher Map Via Strategy Decomposition

**Status:** `░░░░░░░░░░` **0%**
**State:** `PROPOSED`
**Difficulty:** Very High
**Risk:** High — requires substantial new mathematical formalization.

## Core Idea

Abandon the `BottcherSurjOnExterior → contradiction → False.elim → MLC`
chain entirely. Instead, prove `LocallyConnectedSpace mandelbrotSet` by
directly providing the three ingredients to `mlc_strategy_of_branchLocalData`:

```lean
theorem mlc_strategy_of_branchLocalData
    (h_fin_lc :
      ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (_h : FinitelyRenormalizable c),
        LocallyConnectedAt MandelbrotSet ⟨c, hc⟩)
    (h_classify : ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet)
      (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizableTower c)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        LocallyConnectedAt MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace MandelbrotSet
```

## Why This Unsticks Us

- Completely avoids the crude `bottcher_map` and its inconsistency
- Uses the mathematically correct proof strategy (Yoccoz + renormalization)
- Does not require `ExternalRayMapData` or any Böttcher surjectivity claim
- No axioms needed if the three components can be proved constructively

## Implementation Steps

### Step 1: Provide `h_fin_lc` (Yoccoz puzzle → local connectivity)

The codebase already has:
```lean
lemma finite_connectedAt_provider_of_motionHyp
    (h_motion : Quadratic.PuzzleBoundaryMotionHyp) :
    ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet),
      FinitelyRenormalizable c → LocallyConnectedAt MandelbrotSet ⟨c, hc⟩
```

So we need `PuzzleBoundaryMotionHyp`. This captures Yoccoz's theorem on
puzzle piece shrinking. It's currently obtained only via `False.elim`.

**Subgoal:** Prove `PuzzleBoundaryMotionHyp` constructively.
This requires formalizing the Yoccoz puzzle piece shrinking argument:
- Para-puzzle piece nesting and intersection
- The Branner-Hubbard-Yoccoz tableau analysis
- Parameter shrinkage from dynamical shrinkage (already in
  `AxiomsMainConjecture.lean` as `parameter_shrink_of_yoccoz`)

### Step 2: Provide `h_classify` (IR classification)

Need: every infinitely renormalizable parameter is either primitive or
satellite tower. The code has `IRClassificationData` as the target.

**Subgoal:** Prove `IRClassificationData`.
This is a combinatorial argument: the renormalization combinatorics at each
level is either primitive (doubling/tripling) or satellite. The classification
follows from the structure of small copies of the Mandelbrot set.

### Step 3: Provide `h_bridge` (molecule conjecture → satellite LC)

Need: assuming the molecule conjecture, satellite tower parameters are
locally connected.

**Subgoal:** Prove the satellite bridge, or prove `MoleculeConjectureRefined`
directly.

The molecule conjecture is one of the deepest ingredients. This is where the
Dudko-Lyubich renormalization theory applies.

### Step 4: Rewire `mlc_conjecture`

```lean
theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  exact mlc_strategy_of_branchLocalData
    (finite_connectedAt_provider_of_motionHyp h_motion_proof)
    h_classify_proof
    h_bridge_proof
```

## Feasibility Assessment

This is the "correct" mathematical approach but requires formalizing the
three hardest theorems in holomorphic dynamics:
1. Yoccoz's puzzle piece shrinking (the main content of MLC for
   finitely renormalizable parameters)
2. IR combinatorial classification
3. Molecule conjecture / renormalization

Each of these is a research-level formalization project. However, the Yoccoz
library already contains significant puzzle machinery (`Yoccoz.Yoccoz` is
imported), so Step 1 may be partially achievable.

## When to Choose This Plan

- If Plan 01 (fixing bottcher_map) turns out to require too many cascading
  changes
- If the goal is to build a "real" proof of MLC rather than a formal trick
- Long-term: this is the target architecture regardless of other plans
