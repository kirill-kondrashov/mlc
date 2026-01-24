import Mlc.InfinitelyRenormalizable
import Mlc.RenormalizationTypes
import Mlc.MoleculeConjectureBridge
import Mlc.LcAtOfShrink
import Mlc.Quadratic.Complex.BottcherMotion

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
# Global axioms for MLC strategy

These axioms package deep results used in the main conjecture proof outline.
-/

/-- Yoccoz's parameter-shrinkage theorem for finitely renormalizable parameters (axiom). -/
axiom yoccoz_parameter_shrink :
    ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
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
