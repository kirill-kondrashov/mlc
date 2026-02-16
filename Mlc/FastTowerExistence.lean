import Mlc.RenormalizationTypes
import Mlc.SatelliteRenormalizationTower

namespace MLC

open Molecule Complex

/-- Minimal replacement target for the IR bridge used by the main strategy:
    infinitely renormalizable parameters admit a renormalization tower. -/
def InfinitelyRenormalizableHasTowerData : Prop :=
  ∀ c, InfinitelyRenormalizable c → SatelliteRenormalizableTower c

/-- Current axiom-backed construction of the IR tower replacement target. -/
axiom infinitely_renormalizable_has_tower_data :
    InfinitelyRenormalizableHasTowerData

/-- Named wrapper used by the production path. -/
def infinitely_renormalizable_has_tower_data_via_axiom :
    InfinitelyRenormalizableHasTowerData :=
  infinitely_renormalizable_has_tower_data

/-- Single bridge hook: from IR data to a satellite renormalization tower. -/
theorem tower_of_infinitely_renormalizable
    (c : ℂ) (h : InfinitelyRenormalizable c) :
    SatelliteRenormalizableTower c :=
  infinitely_renormalizable_has_tower_data_via_axiom c h

end MLC
