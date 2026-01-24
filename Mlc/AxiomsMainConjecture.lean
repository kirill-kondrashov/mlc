import Mlc.InfinitelyRenormalizable
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mlc.LcAtOfShrink
import Mlc.Quadratic.Complex.BottcherMotion
import Yoccoz.Yoccoz

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
# Global axioms for MLC strategy

These axioms package deep results used in the main conjecture proof outline.
-/

/-- Yoccoz's theorem: divergence of moduli implies dynamical puzzle pieces shrink to `{0}`. -/
def yoccoz_parameter_shrink (c : ℂ) (h : FinitelyRenormalizable c) :
    (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} := by
  apply MLC.yoccoz_theorem
  simpa [FinitelyRenormalizable, NonRenormalizable] using h

/-- Parameter-plane shrinkage derived from Yoccoz's dynamical conclusion (axiom). -/
axiom parameter_shrink_of_yoccoz :
    ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
      (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} →
      (⋂ n, MLC.Quadratic.ParaPuzzlePiece n) = {c}

/-- Existence of Böttcher coordinates on the Mandelbrot set (axiom). -/
axiom bottcher_onM_hyp : MLC.Quadratic.BottcherOnMHyp

/-- Green sublevel connectedness on the Mandelbrot set (axiom). -/
axiom green_sublevel_connected_hyp : MLC.Quadratic.GreenSublevelConnectedHyp

/-- Classification of infinitely renormalizable parameters (axiom). -/
axiom classify_infinitely_renormalizable :
    ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c

/-- Bridge from the Molecule Conjecture to MLC for satellite parameters (axiom). -/
axiom molecule_conjecture_bridge :
    MoleculeConjectureRefined →
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

end MLC
