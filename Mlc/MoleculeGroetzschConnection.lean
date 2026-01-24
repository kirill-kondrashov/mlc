import Mlc.MoleculeToParameterShrink
import Mlc.Quadratic.Complex.GaussianModulusSummable

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-!
Connection note: with the current proxy `modulus` (Gaussian-weighted area), the moduli of
pairwise-disjoint annuli are always summable.

In particular, for any monotone depth selection, the principal nest annuli
`dynAnnulus c depths n` have summable moduli, so a target of the form
`¬ Summable (fun n => modulus (dynAnnulus ... n))` cannot be proved from analytic geometry alone.
-/

namespace PrincipalNestTarget

theorem not_modulusNotSummableTarget (c : ℂ) (hTower : SatelliteRenormalizableTower c) :
    ¬ ModulusNotSummableTarget c hTower := by
  -- The canonical depths from the tower are monotone, hence the principal annuli are pairwise disjoint.
  have hmono : Monotone (depthsFromSatelliteTower c hTower) :=
    depthsFromSatelliteTower_monotone c hTower
  have hs : Summable (fun n =>
      MLC.Quadratic.modulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c (depthsFromSatelliteTower c hTower) n)) :=
    MLC.Quadratic.PrincipalNest.summable_modulus_dynAnnulus c (depthsFromSatelliteTower c hTower) hmono
  intro hdiv
  exact hdiv hs

end PrincipalNestTarget

end

end MLC
