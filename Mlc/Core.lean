import Yoccoz.Yoccoz
import Mlc.LocalConnectivity
import Mlc.ParaPuzzleConnectivity
import Mlc.RenormalizationTypes
import Mlc.MoleculeToSatelliteNestData
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-- The Mandelbrot set used by the root theorem. -/
abbrev mandelbrotSet : Set ℂ := MLC.Quadratic.MandelbrotSet

/-- The two mutually exclusive renormalization sides used by the root assembly. -/
theorem dichotomy (c : ℂ) :
    FinitelyRenormalizable c ∨ InfinitelyRenormalizable c := by
  by_cases h_fin : FinitelyRenormalizable c
  · exact Or.inl h_fin
  · exact Or.inr (infinitelyRenormalizable_of_not_finitelyRenormalizable c h_fin)

/-- Track 1 of the residual near-Molecule program. -/
def IRNoTowerImpliesPrimitiveData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : InfinitelyRenormalizable c),
    ¬ SatelliteRenormalizableTower c → PrimitiveRenormalizable c

/-- Problem 4.3 in the root-facing uniform conformal-modulus form. -/
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  MoleculeBridgeTarget.MoleculeImpliesUniformConformalLowerBoundTarget

/-- Interpolation Problem 4.4 in the root-facing classification form. -/
def Problem44VirtualMoleculeData : Prop :=
  IRNoTowerImpliesPrimitiveData

/-- The explicit open residual for the virtual near-Molecule regime. -/
def ResidualOpenVirtualNearMoleculeData : Prop :=
  Problem43PseudoSiegelAPrioriBoundsData ∧ Problem44VirtualMoleculeData

/-- The remaining Dudko–Lyubich residual used by the root theorem. -/
axiom residualOpenVirtualNearMoleculeAxiom :
  ResidualOpenVirtualNearMoleculeData

/-- Yoccoz shrinkage on the finitely renormalizable branch. -/
theorem parameter_shrink_of_yoccoz
    (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : FinitelyRenormalizable c)
    (h_dyn : (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
  MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton c h_dyn

/-- The Mandelbrot set is locally connected modulo the two explicit frontier inputs. -/
theorem mlc_conjecture :
    LocallyConnectedSpace mandelbrotSet := by
  rcases residualOpenVirtualNearMoleculeAxiom with ⟨h_uniform, h_primitive⟩
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin | h_inf
  · have h_dyn :
        (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} :=
      MLC.yoccoz_theorem c (by
        simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin)
    exact lc_at_of_shrink_of_connected_at c hc
      (para_puzzle_piece_inter_mandelbrot_connected_proved c hc)
      (parameter_shrink_of_yoccoz c hc h_fin h_dyn)
  · by_cases h_tower : SatelliteRenormalizableTower c
    · exact lc_at_of_shrink_of_connected_at c hc
        (para_puzzle_piece_inter_mandelbrot_connected_proved c hc)
        (MoleculeBridgeTarget.parameter_shrink_of_moleculeUniformBridgeTarget
          h_uniform c hc h_tower)
    · exact h_primitive c hc h_inf h_tower hc

end

end MLC
