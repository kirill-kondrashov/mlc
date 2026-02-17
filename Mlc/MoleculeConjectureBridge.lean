import Molecule.Conjecture
import Mlc.LcAtOfShrink
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mlc.RenormalizationTypes
import Mlc.MoleculeToParameterShrink

namespace MLC

open Molecule Set

abbrev MoleculeConjectureRefined : Prop :=
  ∀ (_h_exists :
      ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
        IsCompact P ∧
        Convex ℝ P ∧
        MapsTo (slice_operator f_ref) P P ∧
        K = {f | slice_chart f_ref f ∈ P} ∧
        SurjOn (slice_chart f_ref) K P ∧
        K.Finite ∧
        InjOn (slice_chart f_ref) K ∧
        ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K) ∧
        K.Nonempty ∧
        f_ref ∈ K)
    (_h_conj :
      ∀ f_ref : BMol,
        ∀ x ∈ slice_domain f_ref,
          slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x))
    (_h_norm :
      ∀ K : Set BMol,
        (∀ f ∈ K, IsFastRenormalizable f) ∧
        (∀ f ∈ K, criticalValue f = 0) ∧
        (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1))
    (_h_ps :
      ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
        ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps)
    (_h_orbit :
      ∀ (f_star : BMol) (D : Set ℂ) (U : Set BMol) (a b : ℕ → ℕ),
        Rfast f_star = f_star →
        IsFastRenormalizable f_star →
        IsOpen D → IsOpen U →
        f_star ∈ U →
        criticalValue f_star ∈ D →
        (∀ (n t : ℕ) (f : BMol),
          n ≥ 1 →
          t ∈ ({a n, b n} : Set ℕ) →
          f ∈ (Rfast^[n]) ⁻¹' U →
          MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
          criticalValue f ∈ (Rfast^[n] f).U ∧
          (f.f^[t] (criticalValue f)) ∈ D ∧
          (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
          (∀ y ∈ (Rfast^[n] f).V,
            Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2)))
    (_h_piecewise : IsPiecewiseAnalytic1DUnstable Rfast)
    (_h_shift : ∃ N, IsConjugateToShift Rprm_combinatorial_model N)
    (_h_assoc : CombinatoriallyAssociated Rfast_HMol_candidate Rprm_combinatorial_model)
    (_h_compact : IsCompactOperator Rfast_HMol_candidate)
    (_h_gap :
      ∀ {f_star : BMol} {D : Set ℂ} {U : Set BMol} {a b : ℕ → ℕ},
        HasSiegelBounds f_star D U a b →
        let F := slice_operator f_star
        let φ := slice_chart f_star
        DifferentiableAt ℂ F (φ f_star) ∧
        IsHyperbolic1DUnstable (fderiv ℂ F (φ f_star)))
    (_h_unique :
      ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
               (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2),
  ∃ (Rfast : BMol → BMol)
    (Rfast_HMol : HMol → HMol)
    (R_target : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp}),
    IsHyperbolic Rfast ∧
    IsPiecewiseAnalytic1DUnstable Rfast ∧
    IsCompactOperator Rfast_HMol ∧
    CombinatoriallyAssociated Rfast_HMol R_target ∧
    (∃ N, IsConjugateToShift R_target N)

/-! ### Bridge assumptions

These capture the missing dictionary between quadratic parameters and the Molecule
renormalization objects. They are intended to be discharged by constructing `parameterToBMol`
explicitly and proving its analytic properties. -/

/-- Single replacement target for the remaining Molecule→modulus bridge. -/
def MoleculeModulusLowerBoundData : Prop :=
  ∀ (_h_mol : MoleculeConjectureRefined) (c : ℂ)
    (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c),
    PrincipalNestTarget.ModulusNotSummableTarget c hTower

/-- Phase-2 redesign target: conformal principal-nest modulus divergence data. -/
def MoleculeConformalModulusLowerBoundData : Prop :=
  ∀ (_h_mol : MoleculeConjectureRefined) (c : ℂ)
    (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c),
    PrincipalNestTarget.ConformalModulusNotSummableTarget c hTower

/-- Stronger redesign target: uniform positive conformal-modulus lower bounds
    along canonical tower depths. -/
def MoleculeUniformConformalLowerBoundData : Prop :=
  ∀ (_h_mol : MoleculeConjectureRefined) (c : ℂ)
    (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c),
    PrincipalNestTarget.UniformConformalLowerBoundTarget c hTower

/-- Uniform conformal lower-bound data implies conformal bridge data. -/
theorem moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData
    (h_uniform : MoleculeUniformConformalLowerBoundData) :
    MoleculeConformalModulusLowerBoundData := by
  intro h_mol c hc hTower
  exact PrincipalNestTarget.conformalModulusNotSummableTarget_of_uniformConformalLowerBoundTarget
    c hTower (h_uniform h_mol c hc hTower)

/-- Parameter-piece shrinkage directly from uniform conformal lower-bound data. -/
theorem molecule_parameter_shrink_of_tower_of_uniformConformalLowerBoundData
    (h_uniform : MoleculeUniformConformalLowerBoundData)
    (h_mol : MoleculeConjectureRefined) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  exact PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget c hc hTower
    (h_uniform h_mol c hc hTower)

/-- Under the current model, conformal and Gaussian bridge data are equivalent. -/
theorem moleculeConformalModulusLowerBoundData_iff_moleculeModulusLowerBoundData :
    MoleculeConformalModulusLowerBoundData ↔ MoleculeModulusLowerBoundData := by
  constructor <;> intro h h_mol c hc hTower
  · exact (PrincipalNestTarget.conformalModulusNotSummableTarget_iff_modulusNotSummableTarget c hTower).1
      (h h_mol c hc hTower)
  · exact (PrincipalNestTarget.conformalModulusNotSummableTarget_iff_modulusNotSummableTarget c hTower).2
      (h h_mol c hc hTower)

theorem moleculeConformalModulusLowerBoundData_of_moleculeModulusLowerBoundData
    (h : MoleculeModulusLowerBoundData) : MoleculeConformalModulusLowerBoundData :=
  (moleculeConformalModulusLowerBoundData_iff_moleculeModulusLowerBoundData).2 h

theorem moleculeModulusLowerBoundData_of_moleculeConformalModulusLowerBoundData
    (h : MoleculeConformalModulusLowerBoundData) : MoleculeModulusLowerBoundData :=
  (moleculeConformalModulusLowerBoundData_iff_moleculeModulusLowerBoundData).1 h

theorem moleculeModulusLowerBoundData_of_uniformConformalLowerBoundData
    (h : MoleculeUniformConformalLowerBoundData) : MoleculeModulusLowerBoundData := by
  exact moleculeModulusLowerBoundData_of_moleculeConformalModulusLowerBoundData
    (moleculeConformalModulusLowerBoundData_of_uniformConformalLowerBoundData h)

/-- Parameter-piece shrinkage from an explicit Molecule→modulus bridge datum. -/
theorem molecule_parameter_shrink_of_tower_of_modulusLowerBoundData
    (h_mod : MoleculeModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  have hdiv : PrincipalNestTarget.ModulusNotSummableTarget c hTower :=
    h_mod h_mol c hc hTower
  exact PrincipalNestTarget.paraPuzzle_shrink_of_modulusNotSummableTarget c hc hTower hdiv

/-- Parameter-piece shrinkage from conformal-target bridge data. -/
theorem molecule_parameter_shrink_of_tower_of_conformalModulusLowerBoundData
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  have hdiv : PrincipalNestTarget.ConformalModulusNotSummableTarget c hTower :=
    h_mod h_mol c hc hTower
  exact PrincipalNestTarget.paraPuzzle_shrink_of_conformalModulusNotSummableTarget c hc hTower hdiv

/-- Molecule Conjecture implies parameter-piece shrinkage for satellite parameters. -/
theorem molecule_parameter_shrink_of_tower
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  exact molecule_parameter_shrink_of_tower_of_conformalModulusLowerBoundData
    h_mod h_mol c hc hTower

/-- Legacy satellite-input wrapper for `molecule_parameter_shrink_of_tower`. -/
theorem molecule_parameter_shrink
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined) (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h_sat : SatelliteRenormalizable c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} := by
  exact molecule_parameter_shrink_of_tower h_mod h_mol c hc
    (satelliteRenormalizableTower_of_satelliteRenormalizable c h_sat)

/-- Local connectivity from Molecule shrinkage and a puzzle-boundary motion. -/
theorem refined_conjecture_implies_lc_of_tower_of_modulusLowerBoundData
    (h_mod : MoleculeModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink c hc
    (molecule_parameter_shrink_of_tower_of_modulusLowerBoundData h_mod h_mol c hc hTower)

/-- Local connectivity from conformal-target Molecule shrinkage data. -/
theorem refined_conjecture_implies_lc_of_tower_of_conformalModulusLowerBoundData
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink c hc
    (molecule_parameter_shrink_of_tower_of_conformalModulusLowerBoundData h_mod h_mol c hc hTower)

/-- Local connectivity directly from uniform conformal lower-bound bridge data. -/
theorem refined_conjecture_implies_lc_of_tower_of_uniformConformalLowerBoundData
    (h_uniform : MoleculeUniformConformalLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact lc_at_of_shrink c hc
    (molecule_parameter_shrink_of_tower_of_uniformConformalLowerBoundData
      h_uniform h_mol c hc hTower)

/-- Local connectivity from Molecule shrinkage and a puzzle-boundary motion. -/
theorem refined_conjecture_implies_lc_of_tower
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hTower : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact refined_conjecture_implies_lc_of_tower_of_conformalModulusLowerBoundData
    h_mod h_mol c hc hTower

/-- Legacy satellite-input wrapper for `refined_conjecture_implies_lc_of_tower`. -/
theorem refined_conjecture_implies_lc
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h_sat : SatelliteRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact refined_conjecture_implies_lc_of_tower h_mod h_mol c hc
    (satelliteRenormalizableTower_of_satelliteRenormalizable c h_sat)

/-- The bridge from the Molecule Conjecture to MLC for satellite parameters. -/
theorem molecule_conjecture_bridge_of_tower_of_modulusLowerBoundData
    (h_mod : MoleculeModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact refined_conjecture_implies_lc_of_tower_of_modulusLowerBoundData
    h_mod h_mol c hc _h

/-- Bridge to satellite MLC from conformal-target Molecule bridge data. -/
theorem molecule_conjecture_bridge_of_tower_of_conformalModulusLowerBoundData
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact refined_conjecture_implies_lc_of_tower_of_conformalModulusLowerBoundData
    h_mod h_mol c hc _h

/-- Bridge from Molecule Conjecture to satellite MLC from uniform conformal
    lower-bound data. -/
theorem molecule_conjecture_bridge_of_tower_of_uniformConformalLowerBoundData
    (h_uniform : MoleculeUniformConformalLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact refined_conjecture_implies_lc_of_tower_of_uniformConformalLowerBoundData
    h_uniform h_mol c hc _h

/-- The bridge from the Molecule Conjecture to MLC for satellite parameters. -/
theorem molecule_conjecture_bridge_of_tower
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact molecule_conjecture_bridge_of_tower_of_conformalModulusLowerBoundData
    h_mod h_mol c hc _h

/-- Legacy satellite-input wrapper for `molecule_conjecture_bridge_of_tower`. -/
theorem molecule_conjecture_bridge
    (h_mod : MoleculeConformalModulusLowerBoundData)
    (h_mol : MoleculeConjectureRefined)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact molecule_conjecture_bridge_of_tower h_mod h_mol c hc
    (satelliteRenormalizableTower_of_satelliteRenormalizable c _h)

theorem molecule_conjecture_implies_mlc_satellite
    (h_bridge :
      -- The literature asserts this bridge; see Appendix C of arXiv:1703.01206v3
      -- and Conjecture 1.2 discussion in arXiv:2512.24171v1.
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : SatelliteRenormalizable c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact h_bridge Molecule.molecule_conjecture_refined c hc h

theorem molecule_conjecture_implies_mlc_satellite_of_tower
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizableTower c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩)
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (h : SatelliteRenormalizableTower c) :
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩ := by
  exact h_bridge Molecule.molecule_conjecture_refined c hc h

end MLC
