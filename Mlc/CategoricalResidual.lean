import Mlc.MoleculeToParameterShrink
import Mathlib.CategoryTheory.Limits.Types.Products

namespace MLC

open Molecule

noncomputable section

/-- Track 1 of the residual near-Molecule program. -/
def IRNoTowerImpliesPrimitiveData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (_h : InfinitelyRenormalizable c),
    ¬ SatelliteRenormalizableTower c → PrimitiveRenormalizable c

/-- Problem 4.3 in the root-facing uniform conformal-modulus form. -/
def Problem43PseudoSiegelAPrioriBoundsData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c),
    PrincipalNestTarget.UniformConformalLowerBoundTarget c hTower

/-- Interpolation Problem 4.4 in the root-facing classification form. -/
def Problem44VirtualMoleculeData : Prop :=
  IRNoTowerImpliesPrimitiveData

namespace Categorical

open CategoryTheory CategoryTheory.Limits

/-- The two residual inputs as objects of the category of types. -/
def residualInputCone : BinaryFan (PLift Problem43PseudoSiegelAPrioriBoundsData)
    (PLift Problem44VirtualMoleculeData) :=
  Types.binaryProductCone _ _

/-- The universal product property of the two residual inputs. -/
def residualInputConeIsLimit :
    IsLimit residualInputCone :=
  Types.binaryProductLimit _ _

end Categorical

/-- The residual near-Molecule input as a categorical product witness. -/
def CategoricalResidualOpenVirtualNearMoleculeData : Prop :=
  Nonempty Categorical.residualInputCone.pt

/-- The original root-facing conjunction of the two residual inputs. -/
abbrev ResidualOpenVirtualNearMoleculeData : Prop :=
  Problem43PseudoSiegelAPrioriBoundsData ∧ Problem44VirtualMoleculeData

theorem categoricalResidualOpenVirtualNearMoleculeData_iff :
    CategoricalResidualOpenVirtualNearMoleculeData ↔
      ResidualOpenVirtualNearMoleculeData := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.1.down, h.2.down⟩
  · rintro ⟨h43, h44⟩
    exact ⟨⟨PLift.up h43, PLift.up h44⟩⟩

end

end MLC
