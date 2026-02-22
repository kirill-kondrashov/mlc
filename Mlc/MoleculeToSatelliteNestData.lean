import Mlc.MoleculeConjectureBridge
import Mlc.SatellitePrincipalNestData
import Mlc.SatelliteRenormalizationTower
import Mlc.MoleculeToParameterShrink
import Mlc.LcAtOfShrink

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-!
This file records explicit remaining bridge targets for the Molecule→satellite
part of the MLC strategy.

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
  ∀ (_h_mol : MoleculeConjectureRefined) (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet),
    SatelliteRenormalizableTower c → Nonempty (SatellitePrincipalNestData c)

/-- Canonical-depth variant: produce a uniform conformal lower bound along the
    tower-selected principal annuli. -/
abbrev MoleculeImpliesUniformConformalLowerBoundTarget : Prop :=
  MoleculeUniformConformalLowerBoundData

/-- Canonical-depth strengthening of the principal-nest bridge target. -/
def MoleculeImpliesCanonicalSatellitePrincipalNestData : Prop :=
  ∀ (_h_mol : MoleculeConjectureRefined) (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c),
    ∃ hdata : SatellitePrincipalNestData c,
      hdata.depths = PrincipalNestTarget.depthsFromSatelliteTower c hTower

/-- Compatibility predicate: a principal-nest package uses the tower-selected
    canonical depth schedule. -/
def HasCanonicalDepths (c : ℂ) (hTower : SatelliteRenormalizableTower c)
    (hdata : SatellitePrincipalNestData c) : Prop :=
  hdata.depths = PrincipalNestTarget.depthsFromSatelliteTower c hTower

/--
Once `MoleculeImpliesSatellitePrincipalNestData` is proved, the axiom
`MLC.molecule_parameter_shrink` can be replaced by a theorem (after strengthening
`SatelliteRenormalizable` to a tower-style hypothesis).
-/
theorem parameter_shrink_of_moleculeBridgeTarget
    (hTarget : MoleculeImpliesSatellitePrincipalNestData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  classical
  exact
    paraPuzzle_shrink_of_satellitePrincipalNestData c hc
      (Classical.choice (hTarget h_mol c hc hTower))

/-- Shrinkage from the canonical-depth uniform conformal bridge target. -/
theorem parameter_shrink_of_moleculeUniformBridgeTarget
    (hTarget : MoleculeImpliesUniformConformalLowerBoundTarget)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  exact PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget c hc hTower
    (hTarget h_mol c hc hTower)

/-- Canonical-depth principal-nest data gives the uniform conformal lower-bound
    target used by the redesigned bridge route. -/
theorem uniformConformalLowerBoundTarget_of_satellitePrincipalNestData_of_hasCanonicalDepths
    (c : ℂ) (hTower : SatelliteRenormalizableTower c)
    (hdata : SatellitePrincipalNestData c)
    (hcanon : HasCanonicalDepths c hTower hdata) :
    PrincipalNestTarget.UniformConformalLowerBoundTarget c hTower := by
  rw [HasCanonicalDepths] at hcanon
  rcases hdata.modulus_lower with ⟨m, hm_pos, hm_lb⟩
  refine ⟨m, hm_pos, ?_⟩
  intro n
  have hm_lb' := hm_lb n
  rw [hcanon] at hm_lb'
  have hm_lb'' : m ≤
      MLC.Quadratic.modulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c
          (PrincipalNestTarget.depthsFromSatelliteTower c hTower) n) := hm_lb'
  simpa [MLC.Quadratic.cmodulus] using hm_lb''

/-- Canonical-depth principal-nest bridge data implies the canonical uniform
    conformal bridge target. -/
theorem moleculeUniformBridgeTarget_of_moleculeCanonicalSatellitePrincipalNestData
    (hTarget : MoleculeImpliesCanonicalSatellitePrincipalNestData) :
    MoleculeImpliesUniformConformalLowerBoundTarget := by
  intro h_mol c hc hTower
  rcases hTarget h_mol c hc hTower with ⟨hdata, hcanon⟩
  exact uniformConformalLowerBoundTarget_of_satellitePrincipalNestData_of_hasCanonicalDepths
    c hTower hdata hcanon

/-- Uniform conformal bridge target implies the strong principal-nest bridge
    target by choosing canonical tower depths and reusing the same uniform
    lower bound as Gaussian modulus data. -/
theorem moleculeBridgeTarget_of_moleculeUniformBridgeTarget
    (hTarget : MoleculeImpliesUniformConformalLowerBoundTarget) :
    MoleculeImpliesSatellitePrincipalNestData := by
  intro h_mol c hc hTower
  rcases hTarget h_mol c hc hTower with ⟨μ, hμ_pos, hμ_lb⟩
  refine ⟨{
    depths := PrincipalNestTarget.depthsFromSatelliteTower c hTower
    monotone := PrincipalNestTarget.depthsFromSatelliteTower_monotone c hTower
    cofinal := PrincipalNestTarget.depthsFromSatelliteTower_cofinal c hTower
    modulus_lower := ?_
  }⟩
  refine ⟨μ, hμ_pos, ?_⟩
  intro n
  have hμ_lb' : μ ≤
      MLC.Quadratic.cmodulus
        (MLC.Quadratic.PrincipalNest.dynAnnulus c
          (PrincipalNestTarget.depthsFromSatelliteTower c hTower) n) := hμ_lb n
  simpa [MLC.Quadratic.cmodulus] using hμ_lb'

/-- Local connectivity from the strong satellite principal-nest bridge target. -/
theorem lc_of_moleculeBridgeTarget
    (hTarget : MoleculeImpliesSatellitePrincipalNestData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink c hc
    (parameter_shrink_of_moleculeBridgeTarget hTarget h_mol c hc hTower)

/-- Local connectivity from the canonical-depth uniform conformal bridge target. -/
theorem lc_of_moleculeUniformBridgeTarget
    (hTarget : MoleculeImpliesUniformConformalLowerBoundTarget)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hTower : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink c hc
    (parameter_shrink_of_moleculeUniformBridgeTarget hTarget h_mol c hc hTower)

/-- `mlc_strategy`-compatible satellite bridge generated by the strong principal-nest target. -/
theorem bridge_of_moleculeBridgeTarget
    (hTarget : MoleculeImpliesSatellitePrincipalNestData) :
    MoleculeConjectureRefined →
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  intro h_mol c hc hTower
  exact lc_of_moleculeBridgeTarget hTarget h_mol c hc hTower

/-- `mlc_strategy`-compatible satellite bridge generated by the canonical-depth
    uniform conformal target. -/
theorem bridge_of_moleculeUniformBridgeTarget
    (hTarget : MoleculeImpliesUniformConformalLowerBoundTarget) :
    MoleculeConjectureRefined →
    ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
      MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  intro h_mol c hc hTower
  exact lc_of_moleculeUniformBridgeTarget hTarget h_mol c hc hTower

end MoleculeBridgeTarget

end

end MLC
