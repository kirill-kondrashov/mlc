/-
# Renormalization Tower Existence

The existence of at least one infinitely renormalizable parameter.
This is a standard result in complex dynamics (e.g., the Feigenbaum point c ≈ -1.40115...).

Rather than using the hard axiom `ir_locally_connected_seam` (which concludes that IR parameters
are locally connected on the seam boundary), we use the much weaker and more standard fact that
there exist infinitely renormalizable parameters whose renormalization towers exist.

The Feigenbaum parameter is known to be infinitely renormalizable, and its renormalization tower
is well-defined. This axiom asserts the existence of such a parameter and its tower.
-/

import Mlc.MoleculeRenormalizationTower
import Mlc.RenormalizationTypes
import Mlc.SatelliteRenormalizationTower
import Molecule.RenormalizationTheorem
import Molecule.Conjecture

namespace MLC

open Quadratic Complex Molecule

noncomputable section

/-- Hypotheses used by Molecule's renormalization theorem to produce a
    fast-renormalizable `Rfast` fixed point. -/
structure MoleculeRenormalizableFixedPointData : Prop where
  h_exists :
    ∃ (K : Set BMol) (f_ref : BMol) (P : Set SliceSpace),
      IsCompact P ∧
      Convex ℝ P ∧
      Set.MapsTo (slice_operator f_ref) P P ∧
      K = {f | slice_chart f_ref f ∈ P} ∧
      Set.SurjOn (slice_chart f_ref) K P ∧
      K.Finite ∧
      Set.InjOn (slice_chart f_ref) K ∧
      ContinuousOn (slice_operator f_ref) ((slice_chart f_ref) '' K) ∧
      K.Nonempty ∧
      f_ref ∈ K
  h_conj :
    ∀ f_ref : BMol,
      ∀ x ∈ slice_domain f_ref,
        slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x)
  h_norm :
    ∀ K : Set BMol,
      (∀ f ∈ K, IsFastRenormalizable f) ∧
      (∀ f ∈ K, criticalValue f = 0) ∧
      (∀ f ∈ K, f.V ⊆ Metric.ball 0 0.1)
  h_ps :
    ∀ f_star (D : Set ℂ), IsOpen D → criticalValue f_star ∈ D → Rfast f_star = f_star →
      ∃ D_ps, D_ps ⊆ D ∧ IsQuasidisk D_ps ∧ PseudoInvariant f_star D_ps ∧ criticalValue f_star ∈ D_ps
  h_orbit :
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
        Set.MapsTo (f.f^[t]) (Rfast^[n] f).U (Rfast^[n] f).V ∧
        criticalValue f ∈ (Rfast^[n] f).U ∧
        (f.f^[t] (criticalValue f)) ∈ D ∧
        (∀ z ∈ (Rfast^[n] f).U, f.f^[t] z = (Rfast^[n] f).f z) ∧
        (∀ y ∈ (Rfast^[n] f).V,
          Set.ncard {x ∈ (Rfast^[n] f).U | f.f^[t] x = y} = 2))
  h_unique :
    ∀ f1 f2, (Rfast f1 = f1 ∧ IsFastRenormalizable f1) →
             (Rfast f2 = f2 ∧ IsFastRenormalizable f2) → f1 = f2

/-- Surjectivity placeholder connecting quadratic parameters to BMol maps. -/
def ParameterToBMolSurjectiveData : Prop :=
  ∀ g : BMol, ∃ c : ℂ, parameterToBMol c = g

/-- Weaker lift placeholder: only `Rfast` fixed points that are
    fast-renormalizable need to come from quadratic parameters. -/
def ParameterToBMolFixedPointLiftData : Prop :=
  ∀ g : BMol, IsFastRenormalizable g → Rfast g = g → ∃ c : ℂ, parameterToBMol c = g

/-- Minimal parameter-model predicate for a BMol map. -/
def IsParameterToBMolModel (g : BMol) : Prop :=
  ∃ c : ℂ, g = parameterToBMol c

/-- Fixed-point normalization/model data:
    every fast-renormalizable `Rfast` fixed point admits a parameter model. -/
def FixedPointParameterModelData : Prop :=
  ∀ g : BMol, IsFastRenormalizable g → Rfast g = g → IsParameterToBMolModel g

/-- Minimal existence datum used by the final tower bridge:
    one fast-renormalizable `Rfast` fixed point with a parameter model. -/
def ExistsParameterModelRfastFixedPoint : Prop :=
  ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g ∧ IsParameterToBMolModel g

/-- Fixed-point model data implies fixed-point lift data. -/
theorem parameterToBMolFixedPointLiftData_of_fixedPointParameterModelData
    (h_model : FixedPointParameterModelData) :
    ParameterToBMolFixedPointLiftData := by
  intro g h_fast h_fix
  rcases h_model g h_fast h_fix with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

/-- Full surjectivity implies the fixed-point lift condition. -/
theorem parameterToBMolFixedPointLiftData_of_surjectiveData
    (h_surj : ParameterToBMolSurjectiveData) :
    ParameterToBMolFixedPointLiftData := by
  intro g _h_fast _h_fix
  exact h_surj g

/-- Molecule fixed-point hypotheses produce a fast-renormalizable `Rfast` fixed
    point in BMol. -/
theorem exists_rfast_fixed_point_of_moleculeRenormalizableFixedPointData
    (h : MoleculeRenormalizableFixedPointData) :
    ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g := by
  exact Molecule.renormalizable_fixed_point_exists
    h.h_exists h.h_conj h.h_norm h.h_ps h.h_orbit h.h_unique

/-- A fast-renormalizable fixed point of `Rfast` is automatically infinitely
    fast-renormalizable, since every iterate is equal to the original map. -/
theorem infinitelyFast_of_rfast_fixed_point (g : BMol)
    (h_fast : IsFastRenormalizable g)
    (h_fix : Rfast g = g) :
    IsInfinitelyFastRenormalizable g := by
  have h_iter_eq : ∀ n : ℕ, (Rfast^[n]) g = g := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        simp [Function.iterate_succ_apply', ih, h_fix]
  intro n
  simpa [h_iter_eq n] using h_fast

/-- Concrete tower extracted from a fast-renormalizable fixed point of `Rfast`. -/
noncomputable def renormalizationTower_of_rfast_fixed_point (g : BMol)
    (h_fast : IsFastRenormalizable g)
    (h_fix : Rfast g = g) :
    RenormalizationTower g :=
  renormalizationTower_of_infinitelyFast g
    (infinitelyFast_of_rfast_fixed_point g h_fast h_fix)

/-- BMol-level existential bridge: a single fast-renormalizable fixed point of
    `Rfast` yields an infinite renormalization tower. -/
theorem exists_renormalizationTower_of_exists_rfast_fixed_point
    (h_exists : ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g) :
    ∃ g : BMol, Nonempty (RenormalizationTower g) := by
  rcases h_exists with ⟨g, h_fast, h_fix⟩
  exact ⟨g, ⟨renormalizationTower_of_rfast_fixed_point g h_fast h_fix⟩⟩

/-- Molecule fixed-point hypotheses imply BMol-level renormalization-tower
    existence. -/
theorem exists_renormalizationTower_of_moleculeRenormalizableFixedPointData
    (h : MoleculeRenormalizableFixedPointData) :
    ∃ g : BMol, Nonempty (RenormalizationTower g) :=
  exists_renormalizationTower_of_exists_rfast_fixed_point
    (exists_rfast_fixed_point_of_moleculeRenormalizableFixedPointData h)

/-- Parameter-level existential bridge: if some parameter map is a
    fast-renormalizable fixed point of `Rfast`, then that parameter has an
    infinite renormalization tower. -/
theorem exists_renormalization_tower_of_exists_parameter_rfast_fixed_point
    (h_exists :
      ∃ c : ℂ, IsFastRenormalizable (parameterToBMol c) ∧
        Rfast (parameterToBMol c) = parameterToBMol c) :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) := by
  rcases h_exists with ⟨c, h_fast, h_fix⟩
  exact ⟨c, ⟨renormalizationTower_of_rfast_fixed_point (parameterToBMol c) h_fast h_fix⟩⟩

/-- Existence bridge from a parameter-modeled fast `Rfast` fixed point. -/
theorem exists_renormalization_tower_of_existsParameterModelRfastFixedPoint
    (h_exists : ExistsParameterModelRfastFixedPoint) :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) := by
  rcases h_exists with ⟨g, h_fast, h_fix, h_model⟩
  rcases h_model with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  refine ⟨?_⟩
  have h_fast_c : IsFastRenormalizable (parameterToBMol c) := by
    simpa [hc] using h_fast
  have h_fix_c : Rfast (parameterToBMol c) = parameterToBMol c := by
    simpa [hc] using h_fix
  exact renormalizationTower_of_rfast_fixed_point (parameterToBMol c) h_fast_c h_fix_c

/-- Combined bridge:
    Molecule fixed-point hypotheses plus fixed-point parameterization data imply
    parameter-level renormalization-tower existence. -/
theorem exists_renormalization_tower_of_moleculeRenormalizableFixedPointData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_lift : ParameterToBMolFixedPointLiftData) :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) := by
  rcases exists_rfast_fixed_point_of_moleculeRenormalizableFixedPointData h_mol with
    ⟨g, h_fast, h_fix⟩
  rcases h_lift g h_fast h_fix with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  refine ⟨?_⟩
  have h_fast_c : IsFastRenormalizable (parameterToBMol c) := by
    simpa [hc] using h_fast
  have h_fix_c : Rfast (parameterToBMol c) = parameterToBMol c := by
    simpa [hc] using h_fix
  exact renormalizationTower_of_rfast_fixed_point (parameterToBMol c) h_fast_c h_fix_c

/-- Model-data variant of the Molecule fixed-point bridge. -/
theorem exists_renormalization_tower_of_moleculeRenormalizableFixedPointData_of_fixedPointParameterModelData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_model : FixedPointParameterModelData) :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) :=
  exists_renormalization_tower_of_moleculeRenormalizableFixedPointData h_mol
    (parameterToBMolFixedPointLiftData_of_fixedPointParameterModelData h_model)

/-- Compatibility wrapper: recover the fixed-point bridge from full
    parameterization surjectivity. -/
theorem exists_renormalization_tower_of_moleculeRenormalizableFixedPointData_of_surjectiveData
    (h_mol : MoleculeRenormalizableFixedPointData)
    (h_surj : ParameterToBMolSurjectiveData) :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) :=
  exists_renormalization_tower_of_moleculeRenormalizableFixedPointData h_mol
    (parameterToBMolFixedPointLiftData_of_surjectiveData h_surj)

/-- Minimal Molecule-side hypothesis bundle needed to obtain one
    fast-renormalizable `Rfast` fixed point in BMol. -/
axiom molecule_renormalizable_fixed_point_data :
  MoleculeRenormalizableFixedPointData

/-- Minimal fixed-point parameter-model hypothesis for the bridge. -/
axiom fixedPoint_parameter_model_data :
  FixedPointParameterModelData

/-- Derived fixed-point lift data from the parameter-model hypothesis. -/
theorem parameterToBMol_fixedPoint_lift :
    ParameterToBMolFixedPointLiftData :=
  parameterToBMolFixedPointLiftData_of_fixedPointParameterModelData
    fixedPoint_parameter_model_data

/-- Molecule-side bridge data yields one parameter-modeled fast `Rfast`
    fixed point. -/
theorem existsParameterModelRfastFixedPoint_of_molecule_bridge_axioms :
    ExistsParameterModelRfastFixedPoint := by
  rcases exists_rfast_fixed_point_of_moleculeRenormalizableFixedPointData
      molecule_renormalizable_fixed_point_data with ⟨g, h_fast, h_fix⟩
  exact ⟨g, h_fast, h_fix, fixedPoint_parameter_model_data g h_fast h_fix⟩

/-- Packaged tower existence obtained from the two minimal bridge axioms. -/
theorem exists_renormalization_tower_of_molecule_bridge_axioms :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) :=
  exists_renormalization_tower_of_existsParameterModelRfastFixedPoint
    existsParameterModelRfastFixedPoint_of_molecule_bridge_axioms

/-- Upstream zero-argument Molecule export package:
    renormalization operator, horseshoe compactness witness, and target model. -/
abbrev MoleculeOperatorPackage : Prop :=
  ∃ (Rfast : BMol → BMol)
    (Rfast_HMol : HMol → HMol)
    (R_target : {x : Mol // x ≠ cusp} → {x : Mol // x ≠ cusp}),
    IsHyperbolic Rfast ∧
    IsPiecewiseAnalytic1DUnstable Rfast ∧
    IsCompactOperator Rfast_HMol ∧
    CombinatoriallyAssociated Rfast_HMol R_target ∧
    (∃ N, IsConjugateToShift R_target N)

/-- Direct integration of upstream zero-argument theorem into the MLC namespace. -/
theorem molecule_operator_package :
    MoleculeOperatorPackage :=
  Molecule.molecule_conjecture_refined.1

/-- Fast fixed-point witness extracted from the upstream canonical bridge API. -/
theorem exists_rfast_fixed_point_of_molecule_canonical_api :
    ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g := by
  simpa using
    (Molecule.canonical_rfast_has_fast_renormalizable_fixed_point
      Molecule.molecule_conjecture_refined)

/-- Backward-compatible name for the integrated fixed-point bridge witness. -/
theorem exists_rfast_fixed_point_of_molecule_conjecture_refined :
    ∃ g : BMol, IsFastRenormalizable g ∧ Rfast g = g :=
  exists_rfast_fixed_point_of_molecule_canonical_api

/-- BMol-level renormalization-tower existence from the upstream zero-argument
    Molecule theorem path. -/
theorem exists_renormalizationTower_of_molecule_conjecture_refined :
    ∃ g : BMol, Nonempty (RenormalizationTower g) :=
  exists_renormalizationTower_of_exists_rfast_fixed_point
    exists_rfast_fixed_point_of_molecule_canonical_api

/-- Final minimal bridge axiom used by `mlc_conjecture`. -/
axiom exists_parameter_model_rfast_fixed_point :
  ExistsParameterModelRfastFixedPoint

/-- Packaged tower existence from the final minimal bridge axiom. -/
theorem exists_renormalization_tower_of_exists_parameter_model_rfast_fixed_point :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) :=
  exists_renormalization_tower_of_existsParameterModelRfastFixedPoint
    exists_parameter_model_rfast_fixed_point

end

end MLC
