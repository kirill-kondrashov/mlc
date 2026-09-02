import Mlc.MoleculeConjectureBridge

namespace MLC

namespace MoleculeBridgeTarget

/-! The root-facing Molecule input and its parameter-shrink consequence. -/
abbrev MoleculeImpliesUniformConformalLowerBoundTarget : Prop :=
  MoleculeUniformConformalLowerBoundDirectData

theorem parameter_shrink_of_moleculeUniformBridgeTarget
    (hTarget : MoleculeImpliesUniformConformalLowerBoundTarget)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
  PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget c hTower
    (hTarget c hc hTower)

end MoleculeBridgeTarget

end MLC
