import Mlc.MoleculeToParameterShrink

namespace MLC

open Quadratic

noncomputable section

/-- Root-facing direct form of the uniform conformal lower-bound target. -/
def MoleculeUniformConformalLowerBoundDirectData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c),
    PrincipalNestTarget.UniformConformalLowerBoundTarget c hTower

end

end MLC
