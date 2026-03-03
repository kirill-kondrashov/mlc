import Mlc.InfinitelyRenormalizable
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mlc.LcAtOfShrink
import Mlc.Quadratic.Complex.Bottcher.BottcherOnM
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
axiom parameter_shrink_of_yoccoz :
    ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
      (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} →
      (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c}

end MLC
