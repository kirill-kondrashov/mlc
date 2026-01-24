import Mlc.MoleculeConjectureBridge
import Mlc.SatellitePrincipalNestData
import Mlc.SatelliteRenormalizationTower
import Mlc.MoleculeToParameterShrink

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-!
This file records the precise remaining bridge needed to eliminate the axiom
`MLC.molecule_parameter_shrink`.

What we *have* (proved in this repo):
* if we can produce `SatellitePrincipalNestData c`, then the parameter pieces shrink.
* if we can produce a satellite renormalization tower, we get a canonical cofinal depth function.

What we still *need* (not yet proved):
* Molecule Conjecture + satellite renormalizability ⇒ `SatellitePrincipalNestData c`
  (or at least the corresponding modulus lower bound target for the canonical depths).
-/

namespace MoleculeBridgeTarget

/-- A strong, explicit bridge target: produce DLS principal nest data from Molecule inputs. -/
def MoleculeImpliesSatellitePrincipalNestData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet),
    SatelliteRenormalizableTower c → Nonempty (SatellitePrincipalNestData c)

/--
Once `MoleculeImpliesSatellitePrincipalNestData` is proved, the axiom
`MLC.molecule_parameter_shrink` can be replaced by a theorem (after strengthening
`SatelliteRenormalizable` to a tower-style hypothesis).
-/
theorem parameter_shrink_of_moleculeBridgeTarget
    (hTarget : MoleculeImpliesSatellitePrincipalNestData)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  classical
  exact
    paraPuzzle_shrink_of_satellitePrincipalNestData c hc
      (Classical.choice (hTarget c hc hTower))

end MoleculeBridgeTarget

end

end MLC
