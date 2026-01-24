import Mlc.InfinitelyRenormalizable
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mlc.LcAtOfShrink
import Mlc.Quadratic.Complex.BottcherMotion
import Yoccoz.Yoccoz

namespace MLC

open Quadratic Complex Topology Set Filter

set_option linter.unnecessarySimpa false

/-!
# Global axioms for MLC strategy

These axioms package deep results used in the main conjecture proof outline.
-/

/-- Yoccoz's theorem: divergence of moduli implies dynamical puzzle pieces shrink to `{0}`. -/
def yoccoz_parameter_shrink (c : ℂ) (h : FinitelyRenormalizable c) :
    (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} := by
  apply MLC.yoccoz_theorem
  simpa [FinitelyRenormalizable, NonRenormalizable] using h

/-- Parameter-plane shrinkage derived from Yoccoz's dynamical conclusion. -/
theorem parameter_shrink_of_yoccoz :
    ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
      (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} →
      (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  intro c _hc _h h_dyn
  ext z
  constructor
  · intro hz
    have hz' : z - c ∈ ⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0 := by
      refine Set.mem_iInter.mpr ?_
      intro n
      have : z ∈ MLC.Quadratic.ParaPuzzlePieceAt c n := (Set.mem_iInter.mp hz) n
      have : z - c ∈ MLC.Quadratic.DynamicalPuzzlePiece c n 0 := by
        simpa [MLC.Quadratic.ParaPuzzlePieceAt] using this
      exact this
    have hz_eq : z - c = 0 := by
      have : z - c ∈ ({0} : Set ℂ) := by simpa [h_dyn] using hz'
      simpa using (Set.mem_singleton_iff.mp this)
    have : z = c := sub_eq_zero.mp hz_eq
    simpa [this]
  · intro hz
    have hz' : z = c := by simpa using (Set.mem_singleton_iff.mp hz)
    refine Set.mem_iInter.mpr ?_
    intro n
    have : z - c ∈ MLC.Quadratic.DynamicalPuzzlePiece c n 0 := by
      have h0 : 0 ∈ MLC.Quadratic.DynamicalPuzzlePiece c n 0 := by
        have : 0 ∈ ({0} : Set ℂ) := by simp
        have : 0 ∈ ⋂ k, MLC.Quadratic.DynamicalPuzzlePiece c k 0 := by
          simpa [h_dyn] using this
        exact Set.mem_iInter.mp this n
      simpa [hz'] using h0
    have : z ∈ MLC.Quadratic.ParaPuzzlePieceAt c n := by
      simpa [MLC.Quadratic.ParaPuzzlePieceAt, hz'] using this
    exact this

/-- Existence of Böttcher coordinates on the Mandelbrot set (axiom). -/
axiom bottcher_onM_hyp : MLC.Quadratic.BottcherOnMHyp

/-- Green sublevel connectedness on the Mandelbrot set (axiom). -/
axiom green_sublevel_connected_hyp : MLC.Quadratic.GreenSublevelConnectedHyp

/-- Classification of infinitely renormalizable parameters (axiom). -/
axiom classify_infinitely_renormalizable :
    ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c


end MLC
