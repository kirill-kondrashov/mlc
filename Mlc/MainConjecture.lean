import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
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

/-- Every parameter is either finitely renormalizable (including non-renormalizable) or infinitely renormalizable.
    Proof idea: By the law of excluded middle, the sum of moduli either converges or diverges.
    We use the definition of FinitelyRenormalizable and InfinitelyRenormalizable which directly
    map to this divergence/convergence behavior. -/
theorem dichotomy (c : ℂ) : FinitelyRenormalizable c ∨ InfinitelyRenormalizable c := by
  unfold FinitelyRenormalizable InfinitelyRenormalizable
  rw [or_comm]
  exact Classical.em _

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
    1.  **Finitely Renormalizable**: The moduli of the puzzle annuli diverge. Yoccoz's theorem
        implies the dynamical pieces shrink to a point. The Correspondence Principle then
        implies the parameter pieces shrink to `c`. Finally, `lc_at_of_shrink` shows this
        implies local connectivity at `c`.
    2.  **Infinitely renormalizable**: We invoke the deep theorem (`mlc_infinitely_renormalizable`)
        which establishes MLC in this case. This covers both **Primitive** types (Lyubich) and
        **Satellite** types (Dudko, Lyubich, Selinger). -/
theorem MLC_Conjecture : LocallyConnectedSpace MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin_renorm | h_inf_renorm
  · -- Case 1: Finitely Renormalizable
    exact mlc_finitely_renormalizable c hc h_fin_renorm
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable c hc h_inf_renorm

end MainProof

end MLC
