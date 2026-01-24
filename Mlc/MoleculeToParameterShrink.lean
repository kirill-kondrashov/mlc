import Mlc.SatelliteRenormalizationTower
import Mlc.Quadratic.Complex.PrincipalNestShrink

namespace MLC

open Quadratic Complex Topology Set Filter Molecule

noncomputable section

/-!
Reducing `molecule_parameter_shrink` to a concrete analytic target.

To eliminate the current axiom `MLC.molecule_parameter_shrink`, we need to build a DLS-style
principal nest for satellite renormalizable parameters and prove uniform modulus bounds for
its annuli.

This file makes that target explicit and shows that *once* it is proved, the para-puzzle pieces
shrink to `{c}` by Grötzsch's criterion.
-/

namespace PrincipalNestTarget

def depthsFromSatelliteTower (c : ℂ) (h : SatelliteRenormalizableTower c) : ℕ → ℕ :=
  RenormalizationTower.cumulativePeriod (satelliteTower c h)

theorem depthsFromSatelliteTower_monotone (c : ℂ) (h : SatelliteRenormalizableTower c) :
    Monotone (depthsFromSatelliteTower c h) :=
  satelliteTower_depths_monotone c h

theorem depthsFromSatelliteTower_cofinal (c : ℂ) (h : SatelliteRenormalizableTower c) :
    MLC.Quadratic.PrincipalNest.Cofinal (depthsFromSatelliteTower c h) :=
  satelliteTower_depths_cofinal c h

/-- The remaining analytic target: divergence (non-summability) of principal nest annulus moduli. -/
def ModulusNotSummableTarget (c : ℂ) (h : SatelliteRenormalizableTower c) : Prop :=
  ¬ Summable (fun n =>
    MLC.Quadratic.modulus
      (MLC.Quadratic.PrincipalNest.dynAnnulus c (depthsFromSatelliteTower c h) n))

theorem paraPuzzle_shrink_of_modulusNotSummableTarget (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) (hdiv : ModulusNotSummableTarget c hTower) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  exact
    MLC.Quadratic.PrincipalNest.para_iInter_eq_singleton_of_principal_modulus_not_summable
      c hc
      (depthsFromSatelliteTower c hTower)
      (depthsFromSatelliteTower_monotone c hTower)
      (depthsFromSatelliteTower_cofinal c hTower)
      hdiv

end PrincipalNestTarget

end

end MLC
