import Mlc.RenormalizationTypes
import Mlc.MoleculeRenormalizationTower

namespace MLC

noncomputable section

/-- The root-facing satellite input is an infinite renormalization tower. -/
abbrev SatelliteRenormalizableTower (c : ℂ) : Prop :=
  Nonempty (RenormalizationTower (parameterToBMol c))

noncomputable def satelliteTower (c : ℂ) (h : SatelliteRenormalizableTower c) :
    RenormalizationTower (parameterToBMol c) :=
  Classical.choice h

theorem satelliteTower_depths_monotone (c : ℂ) (h : SatelliteRenormalizableTower c) :
    Monotone (RenormalizationTower.cumulativePeriod (satelliteTower c h)) :=
  RenormalizationTower.cumulativePeriod_monotone (satelliteTower c h)

end

end MLC
