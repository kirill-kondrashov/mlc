import Mlc.FastTowerExistence
import Mlc.MoleculeConjectureBridge
import Mlc.MoleculeGroetzschConnection
import Mlc.Quadratic.Complex.GaussianModulusSummable

namespace MLC

open Complex Topology Set Filter

noncomputable section

/-- `0` belongs to the Mandelbrot set (`boundedOrbit 0 0`). -/
lemma zero_mem_mandelbrotSet_fastTower : (0 : ℂ) ∈ MLC.Quadratic.MandelbrotSet := by
  refine ⟨0, ?_⟩
  intro n
  have horbit : MLC.Quadratic.orbit 0 0 n = 0 := by
    induction n with
    | zero =>
        simp [MLC.Quadratic.orbit]
    | succ n ih =>
        simpa [MLC.Quadratic.orbit_succ, MLC.Quadratic.fc, ih]
  simp [horbit]

/-- Under the Gaussian proxy `modulus`, every parameter is infinitely renormalizable
    by definition (`Summable` puzzle-annulus moduli). -/
lemma infinitely_renormalizable_of_gaussian_modulus (c : ℂ) :
    InfinitelyRenormalizable c := by
  unfold InfinitelyRenormalizable
  simpa [MLC.Quadratic.PrincipalNest.dynAnnulus_id] using
    (MLC.Quadratic.PrincipalNest.summable_modulus_dynAnnulus c (fun n => n) monotone_id)

/-- With the current bridge axioms and Gaussian proxy modulus, no satellite tower can
    exist on Mandelbrot parameters. -/
lemma not_satelliteRenormalizableTower_of_mem_mandelbrot
    (h_mod : MoleculeModulusLowerBoundData) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) :
    ¬ SatelliteRenormalizableTower c := by
  intro hTower
  have hdiv : PrincipalNestTarget.ModulusNotSummableTarget c hTower :=
    h_mod Molecule.molecule_conjecture_refined c hc hTower
  exact PrincipalNestTarget.not_modulusNotSummableTarget c hTower hdiv

/-- Current obstruction: the Phase 3 target is inconsistent with the
    Molecule bridge axiom plus Gaussian proxy modulus. -/
theorem not_infinitely_renormalizable_has_tower_data :
    MoleculeModulusLowerBoundData →
    ¬ InfinitelyRenormalizableHasTowerData := by
  intro h_mod hdata
  have hIR0 : InfinitelyRenormalizable (0 : ℂ) :=
    infinitely_renormalizable_of_gaussian_modulus 0
  have hTower0 : SatelliteRenormalizableTower (0 : ℂ) := hdata 0 hIR0
  exact
    (not_satelliteRenormalizableTower_of_mem_mandelbrot h_mod 0 zero_mem_mandelbrotSet_fastTower)
      hTower0

/-- Any concrete IR→tower bridge datum contradicts the current Gaussian proxy setup. -/
theorem false_of_infinitely_renormalizable_has_tower_data
    (h_mod : MoleculeModulusLowerBoundData)
    (hdata : InfinitelyRenormalizableHasTowerData) : False := by
  exact not_infinitely_renormalizable_has_tower_data h_mod hdata

end
