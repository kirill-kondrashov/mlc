import Yoccoz.Yoccoz
import Mlc.LocalConnectivity
import Mlc.ParaPuzzleConnectivity
import Mlc.RenormalizationTypes
import Mlc.MoleculeToParameterShrink
import Mlc.CategoricalResidual
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

/-- The remaining Dudko–Lyubich residual as a categorical product witness. -/
axiom residualOpenVirtualNearMoleculeAxiom :
  CategoricalResidualOpenVirtualNearMoleculeData

/-- Yoccoz shrinkage on the finitely renormalizable branch. -/
theorem parameter_shrink_of_yoccoz
    (c : ℂ)
    (h_dyn : (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
  MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton c h_dyn

/-- The Mandelbrot set is locally connected modulo the two explicit frontier inputs. -/
theorem mlc_conjecture :
    LocallyConnectedSpace mandelbrotSet := by
  rcases residualOpenVirtualNearMoleculeAxiom with ⟨h_residual⟩
  have h_uniform : Problem43PseudoSiegelAPrioriBoundsData := h_residual.1.down
  have h_primitive : Problem44VirtualMoleculeData := h_residual.2.down
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro ⟨c, hc⟩ U hU
  rcases dichotomy c with h_fin | h_inf
  · have h_dyn :
        (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} :=
      MLC.yoccoz_theorem c (by
        simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin)
    exact preconnected_nhds_of_shrink_of_connected_at c hc
      (para_puzzle_piece_inter_mandelbrot_connected_proved c hc)
      (parameter_shrink_of_yoccoz c h_dyn) U hU
  · by_cases h_tower : SatelliteRenormalizableTower c
    · exact preconnected_nhds_of_shrink_of_connected_at c hc
        (para_puzzle_piece_inter_mandelbrot_connected_proved c hc)
        (PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget
          c h_tower (h_uniform c hc h_tower)) U hU
    · exact h_primitive c hc h_inf h_tower hc U hU

end

end MLC
