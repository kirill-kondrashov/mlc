import Mlc.CategoricalMandelbrot
import Mlc.CategoricalResidual
import Mlc.LocalConnectivity
import Mlc.MoleculeToParameterShrink
import Mlc.RenormalizationTypes
import Mathlib.Topology.Connected.LocallyConnected
import Yoccoz.Yoccoz

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-- The Mandelbrot set used by both root formulations. -/
abbrev mandelbrotSet : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

/-- The remaining Dudko--Lyubich input, exposed at the categorical root. -/
axiom residualOpenVirtualNearMoleculeAxiom :
  CategoricalResidualOpenVirtualNearMoleculeData

/-- The two mutually exclusive renormalization sides used by the root
    assembly. -/
theorem dichotomy (c : ℂ) :
    FinitelyRenormalizable c ∨ InfinitelyRenormalizable c := by
  by_cases h_fin : FinitelyRenormalizable c
  · exact Or.inl h_fin
  · exact Or.inr (infinitelyRenormalizable_of_not_finitelyRenormalizable c h_fin)

/-- Yoccoz shrinkage on the finitely renormalizable branch. -/
theorem parameter_shrink_of_yoccoz
    (c : ℂ)
    (h_dyn : (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
  MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton c h_dyn

namespace Categorical

open CategoryTheory

/-- The Mandelbrot set as an object of `TopCat`. -/
abbrev mandelbrotObject : TopCat :=
  TopCat.of MLC.mandelbrotSet

/-- Local connectedness expressed as a property of a `TopCat` object. -/
def IsLocallyConnectedObject (X : TopCat) : Prop :=
  @LocallyConnectedSpace X X.str

/-- The categorical formulation of the Mandelbrot local-connectivity
    conjecture. -/
def MLCConjecture : Prop :=
  IsLocallyConnectedObject mandelbrotObject

/-- The categorical target is definitionally the usual subspace target. -/
theorem mlcConjecture_iff_set :
    MLCConjecture ↔ LocallyConnectedSpace MLC.mandelbrotSet :=
  Iff.rfl

/-- The root assembly in categorical form. -/
theorem categorical_mlc_conjecture :
    MLCConjecture := by
  change LocallyConnectedSpace MLC.mandelbrotSet
  rcases MLC.residualOpenVirtualNearMoleculeAxiom with ⟨h_residual⟩
  have h_uniform : Problem43PseudoSiegelAPrioriBoundsData := h_residual.1.down
  have h_primitive : Problem44VirtualMoleculeData := h_residual.2.down
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro ⟨c, hc⟩ U hU
  rcases MLC.dichotomy c with h_fin | h_inf
  · have h_dyn :
        (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} :=
      MLC.yoccoz_theorem c (by
        simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin)
    exact preconnected_nhds_of_shrink_of_connected_at c hc
      (para_puzzle_piece_inter_mandelbrot_connected_proved c hc)
      (MLC.parameter_shrink_of_yoccoz c h_dyn) U hU
  · by_cases h_tower : SatelliteRenormalizableTower c
    · exact preconnected_nhds_of_shrink_of_connected_at c hc
        (para_puzzle_piece_inter_mandelbrot_connected_proved c hc)
        (PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget
          c h_tower (h_uniform c hc h_tower)) U hU
    · exact h_primitive c hc h_inf h_tower hc U hU

/-- The usual and categorical root propositions are equivalent. -/
theorem mlc_conjecture_iff_categorical :
    LocallyConnectedSpace MLC.mandelbrotSet ↔ MLCConjecture :=
  mlcConjecture_iff_set.symm

end Categorical

end

end MLC
