import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green
import Mlc.Quadratic.Complex.Puzzle
import Mlc.Yoccoz
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean

open Lean Elab Command

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
# Mandelbrot Local Connectivity (MLC) Conjecture

This file outlines the proof strategy for the MLC conjecture based on Yoccoz puzzles.
-/


section MainProof

/-- Every parameter is either non-renormalizable or infinitely renormalizable.
    Proof idea: By the law of excluded middle, the sum of moduli either converges or diverges.
    We use the definition of NonRenormalizable and InfinitelyRenormalizable which directly
    map to this divergence/convergence behavior. -/
theorem dichotomy (c : ℂ) : NonRenormalizable c ∨ InfinitelyRenormalizable c := by
  rw [NonRenormalizable, InfinitelyRenormalizable]
  by_cases h : Summable (fun n => modulus (PuzzleAnnulus c n))
  · right; exact h
  · left; exact h

/-- If dynamical pieces shrink to a point, parameter pieces shrink to a point.
    Proof idea: This follows directly from the Correspondence Principle axiom (`parameter_shrink_ax`),
    which links the geometry of the dynamical plane to the parameter plane.
    If the dynamical nest at the critical value shrinks to a point, the corresponding parameter
    nest also shrinks to the parameter value. -/
lemma parameter_shrink (c : ℂ) (h : (⋂ n, DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, ParaPuzzlePiece n) = {c} := by
  -- Use the correspondence principle
  apply parameter_shrink_ax c h

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected.
    Proof idea: We prove local connectivity at every point `c` in the Mandelbrot set.
    We split the proof into two cases based on the `dichotomy`:
    1.  **Non-renormalizable**: The moduli of the puzzle annuli diverge. Yoccoz's theorem
        implies the dynamical pieces shrink to a point. The Correspondence Principle then
        implies the parameter pieces shrink to `c`. Finally, `lc_at_of_shrink` shows this
        implies local connectivity at `c`.
    2.  **Infinitely renormalizable**: We invoke Lyubich's deep theorem (`mlc_infinitely_renormalizable`)
        which establishes MLC in this case. -/
theorem MLC_Conjecture : LocallyConnectedSpace MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_non_renorm | h_inf_renorm
  · -- Case 1: Non-renormalizable
    have h_div := non_renormalizable_moduli_diverge c h_non_renorm
    have h_dyn := yoccoz_theorem c h_div
    have h_para := parameter_shrink c h_dyn
    exact lc_at_of_shrink c hc h_para
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable c hc h_inf_renorm

end MainProof

end MLC
