import Mlc.InfinitelyRenormalizable
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mlc.LcAtOfShrink
import Mlc.Quadratic.Complex.Bottcher.BottcherOnM
import Mlc.Quadratic.Complex.PrincipalNestShrink
import Mlc.GreenSublevelConnected
import Yoccoz.Yoccoz

namespace MLC

open Quadratic Complex Topology Set Filter

set_option linter.unnecessarySimpa false

/-!
# Global axioms for MLC strategy

These axioms package deep results used in the main conjecture proof outline.
-/

/-- Parameter-plane shrinkage derived from Yoccoz's dynamical conclusion. -/
theorem parameter_shrink_of_yoccoz :
    ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
      (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} →
      (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  intro c _hc _h h_dyn
  exact MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton c h_dyn

end MLC
