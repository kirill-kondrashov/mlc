import Mlc.RenormalizationTypes
import Mlc.SatelliteRenormalizationTower

namespace MLC

open Molecule Complex

/-- Minimal replacement target for the IR bridge used by the main strategy:
    infinitely renormalizable parameters admit a renormalization tower. -/
def InfinitelyRenormalizableHasTowerData : Prop :=
  ∀ c, InfinitelyRenormalizable c → SatelliteRenormalizableTower c

/-- Single bridge hook: from IR data to a satellite renormalization tower. -/
theorem tower_of_infinitely_renormalizable
    (h_data : InfinitelyRenormalizableHasTowerData)
    (c : ℂ) (h : InfinitelyRenormalizable c) :
    SatelliteRenormalizableTower c :=
  h_data c h

end MLC
