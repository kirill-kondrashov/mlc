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
        simp [MLC.Quadratic.orbit_succ, MLC.Quadratic.fc, ih]
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

/-- Any single Mandelbrot satellite tower refutes the current Gaussian-target bridge data. -/
theorem not_moleculeModulusLowerBoundData_of_mem_mandelbrot_tower
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    ¬ MoleculeModulusLowerBoundData := by
  intro h_mod
  exact (not_satelliteRenormalizableTower_of_mem_mandelbrot h_mod c hc) hTower

/-- Globalized version of the Gaussian-target obstruction. -/
theorem not_moleculeModulusLowerBoundData_of_exists_mem_mandelbrot_tower :
    (∃ c, c ∈ MLC.Quadratic.MandelbrotSet ∧ SatelliteRenormalizableTower c) →
    ¬ MoleculeModulusLowerBoundData := by
  intro h_exists h_mod
  rcases h_exists with ⟨c, hc, hTower⟩
  exact (not_satelliteRenormalizableTower_of_mem_mandelbrot h_mod c hc) hTower

/-- Conformal-target variant of the same obstruction. -/
lemma not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal
    (h_mod : MoleculeConformalModulusLowerBoundData) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) :
    ¬ SatelliteRenormalizableTower c := by
  intro hTower
  have hdiv : PrincipalNestTarget.ConformalModulusNotSummableTarget c hTower :=
    h_mod Molecule.molecule_conjecture_refined c hc hTower
  exact PrincipalNestTarget.not_conformalModulusNotSummableTarget c hTower hdiv

/-- Any single Mandelbrot satellite tower refutes conformal-target bridge data. -/
theorem not_moleculeConformalModulusLowerBoundData_of_mem_mandelbrot_tower
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    ¬ MoleculeConformalModulusLowerBoundData := by
  intro h_mod
  exact (not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal h_mod c hc) hTower

/-- Globalized version of the conformal-target obstruction. -/
theorem not_moleculeConformalModulusLowerBoundData_of_exists_mem_mandelbrot_tower :
    (∃ c, c ∈ MLC.Quadratic.MandelbrotSet ∧ SatelliteRenormalizableTower c) →
    ¬ MoleculeConformalModulusLowerBoundData := by
  intro h_exists h_mod
  rcases h_exists with ⟨c, hc, hTower⟩
  exact (not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal h_mod c hc) hTower

/-- Uniform conformal-target variant: any Mandelbrot satellite tower refutes the
    stronger uniform bridge data. -/
lemma not_satelliteRenormalizableTower_of_mem_mandelbrot_uniform
    (h_uniform : MoleculeUniformConformalLowerBoundData) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) :
    ¬ SatelliteRenormalizableTower c := by
  have h_conf : MoleculeConformalModulusLowerBoundData :=
    moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData h_uniform
  exact not_satelliteRenormalizableTower_of_mem_mandelbrot_conformal h_conf c hc

/-- Uniform conformal-target variant: any Mandelbrot satellite tower refutes the
    stronger uniform bridge data. -/
theorem not_moleculeUniformConformalLowerBoundData_of_mem_mandelbrot_tower
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    ¬ MoleculeUniformConformalLowerBoundData := by
  intro h_uniform
  exact (not_satelliteRenormalizableTower_of_mem_mandelbrot_uniform h_uniform c hc) hTower

/-- Globalized version of the uniform conformal-target obstruction. -/
theorem not_moleculeUniformConformalLowerBoundData_of_exists_mem_mandelbrot_tower :
    (∃ c, c ∈ MLC.Quadratic.MandelbrotSet ∧ SatelliteRenormalizableTower c) →
    ¬ MoleculeUniformConformalLowerBoundData := by
  intro h_exists h_uniform
  rcases h_exists with ⟨c, hc, hTower⟩
  exact (not_moleculeUniformConformalLowerBoundData_of_mem_mandelbrot_tower c hc hTower) h_uniform

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

/-- Combined obstruction: current Gaussian-target Molecule bridge data and
    global IR→tower data are inconsistent. -/
theorem false_of_moleculeModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
    (h_mod : MoleculeModulusLowerBoundData)
    (hdata : InfinitelyRenormalizableHasTowerData) : False := by
  exact not_infinitely_renormalizable_has_tower_data h_mod hdata

/-- Conformal-target variant of the combined obstruction. -/
theorem false_of_moleculeConformalModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (hdata : InfinitelyRenormalizableHasTowerData) : False := by
  have h_mod' : MoleculeModulusLowerBoundData :=
    moleculeModulusLowerBoundData_of_moleculeConformalModulusLowerBoundData h_mod
  exact false_of_moleculeModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
    h_mod' hdata

/-- Phase-1 consistency checkpoint for the active MLC architecture:
    if the conformal Molecule bridge data is assumed, then global IR→tower
    data cannot be simultaneously assumed in the current model. -/
theorem consistency_checkpoint_conformal_bridge_excludes_global_ir_tower
    (h_mod : MoleculeConformalModulusLowerBoundData) :
    ¬ InfinitelyRenormalizableHasTowerData := by
  intro hdata
  exact false_of_moleculeConformalModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
    h_mod hdata

/-- Uniform conformal-target variant of the combined obstruction. -/
theorem false_of_moleculeUniformConformalLowerBoundData_and_infinitely_renormalizable_has_tower_data
    (h_uniform : MoleculeUniformConformalLowerBoundData)
    (hdata : InfinitelyRenormalizableHasTowerData) : False := by
  have h_mod : MoleculeModulusLowerBoundData :=
    moleculeModulusLowerBoundData_of_uniformConformalLowerBoundData h_uniform
  exact false_of_moleculeModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
    h_mod hdata

/-- Any concrete IR→tower bridge datum contradicts the current Gaussian proxy setup. -/
theorem false_of_infinitely_renormalizable_has_tower_data
    (h_mod : MoleculeModulusLowerBoundData)
    (hdata : InfinitelyRenormalizableHasTowerData) : False := by
  exact false_of_moleculeModulusLowerBoundData_and_infinitely_renormalizable_has_tower_data
    h_mod hdata

end
