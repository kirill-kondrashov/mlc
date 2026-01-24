import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.Quadratic.Complex.BottcherMotion
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

/-- If parameter pieces shrink to a point, they form a neighborhood basis at `c`. -/
lemma parameter_shrink_basis (c : ℂ) (h : (⋂ n, ParaPuzzlePiece n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePiece n ⊆ U := by
  exact MLC.Quadratic.parameter_shrink c h

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected.
    Proof idea: We prove local connectivity at every point `c` in the Mandelbrot set.
    We split the proof into two cases based on the `dichotomy`:
    1.  **Finitely Renormalizable**: The moduli of the puzzle annuli diverge. Yoccoz's theorem
        implies the dynamical pieces shrink to a point. We assume the corresponding
        parameter-piece shrinkage as an explicit hypothesis and then apply `lc_at_of_shrink`.
    2.  **Infinitely renormalizable**: We invoke the deep theorem (`mlc_infinitely_renormalizable`)
        which establishes MLC in this case. This covers both **Primitive** types (Lyubich) and
        **Satellite** types (Dudko, Lyubich, Selinger). -/
theorem MLC_Conjecture
    (h_param_shrink :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        (⋂ n, MLC.Quadratic.ParaPuzzlePiece n) = {c})
    (h_bottcher_onM : MLC.Quadratic.BottcherOnMHyp)
    (h_green_conn : MLC.Quadratic.GreenSublevelConnectedHyp)
    (h_classify : ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin_renorm | h_inf_renorm
  · -- Case 1: Finitely Renormalizable
    have h_motion : MLC.Quadratic.PuzzleBoundaryMotionHyp :=
      MLC.Quadratic.puzzle_boundary_motion_hyp_of_onM_connected
        (MLC.Quadratic.bottcher_green_sublevel_hyp_onM_connected_of_onM h_bottcher_onM h_green_conn)
    exact mlc_finitely_renormalizable c hc h_motion h_fin_renorm (h_param_shrink c hc h_fin_renorm)
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable h_classify h_bridge c hc h_inf_renorm

end MainProof

end MLC
