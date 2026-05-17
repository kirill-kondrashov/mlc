import Yoccoz.Quadratic.Complex.Groetzsch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MLC
namespace Quadratic

open MeasureTheory BigOperators Set

noncomputable def cmodulus := modulus

/-- Abstract interface for a true conformal modulus on annulus-like sets.
    The current `cmodulus` remains the Gaussian proxy inherited from the Yoccoz
    package; primitive-Feigenbaum work that genuinely needs conformal invariance
    should target this theorem surface instead of using the proxy definitionally. -/
structure AnnulusConformalModulusAPI where
  mod : Set ℂ → ℝ
  nonneg : ∀ A : Set ℂ, 0 ≤ mod A
  affine_invariant :
    ∀ (A : Set ℂ) (a b : ℂ), a ≠ 0 → mod ((fun z : ℂ => a * z + b) '' A) = mod A

/-- Existence of a genuine conformal-modulus API. This keeps the new route
    separate from the Gaussian proxy while giving downstream theorems a named
    theorem-facing handle. -/
def TrueConformalModulusData : Prop :=
  Nonempty AnnulusConformalModulusAPI

/-- Chosen true conformal-modulus API associated to `TrueConformalModulusData`. -/
noncomputable def chosenTrueConformalModulus
    (h : TrueConformalModulusData) : AnnulusConformalModulusAPI :=
  Classical.choice h

theorem chosenTrueConformalModulus_nonneg
    (h : TrueConformalModulusData) (A : Set ℂ) :
    0 ≤ (chosenTrueConformalModulus h).mod A :=
  (chosenTrueConformalModulus h).nonneg A

theorem chosenTrueConformalModulus_affine_invariant
    (h : TrueConformalModulusData) (A : Set ℂ) (a b : ℂ) (ha : a ≠ 0) :
    (chosenTrueConformalModulus h).mod ((fun z : ℂ => a * z + b) '' A) =
      (chosenTrueConformalModulus h).mod A :=
  (chosenTrueConformalModulus h).affine_invariant A a b ha

/-- Modulus is monotonic. -/
theorem cmodulus_le_of_subset {A B : Set ℂ} (h : A ⊆ B) (_hA : NullMeasurableSet A volume) :
    cmodulus A ≤ cmodulus B := by
  unfold cmodulus modulus
  apply integral_mono_measure (Measure.restrict_mono h le_rfl)
  · apply ae_restrict_of_ae
    apply ae_of_all
    intro z
    exact le_of_lt (Real.exp_pos _)
  · exact weight_integrable.integrableOn

/-- Modulus is additive on finite disjoint unions. -/
theorem cmodulus_finset_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {A : ι → Set ℂ}
    (h_disj : PairwiseDisjoint s A) (h_meas : ∀ i ∈ s, NullMeasurableSet (A i) volume) :
    cmodulus (⋃ i ∈ s, A i) = ∑ i ∈ s, cmodulus (A i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [cmodulus, modulus_empty]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    simp
    simp [cmodulus] at ih ⊢
    unfold modulus
    rw [integral_union_ae]
    · rw [← modulus]
      rw [← modulus]
      rw [ih]
      · rfl
      · apply Set.PairwiseDisjoint.subset h_disj
        simp only [Finset.coe_insert]
        apply Set.subset_insert
      · intro j hj
        exact h_meas j (Finset.mem_insert_of_mem hj)
    · -- Disjointness
      apply Disjoint.aedisjoint
      rw [Set.disjoint_right]
      intro z h_union h_i
      simp only [Set.mem_iUnion] at h_union
      rcases h_union with ⟨j, hj_s, h_z_j⟩
      have h_neq : i ≠ j := ne_comm.mp (ne_of_mem_of_not_mem hj_s hi)
      have h_disj_ij := h_disj (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj_s) h_neq
      exact Set.disjoint_left.1 h_disj_ij h_i h_z_j
    · -- Measurability of Union (2nd arg)
      apply NullMeasurableSet.biUnion s.finite_toSet.countable
      intro j hj
      exact h_meas j (Finset.mem_insert_of_mem hj)
    · -- Integrability A i
      exact weight_integrable.integrableOn
    · -- Integrability Union
      exact weight_integrable.integrableOn

theorem cgroetzsch_criterion {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (h_zero : ∀ n, 0 ∈ P n)
    (h_conn : ∀ n, IsConnected (P n))
    (h_meas : ∀ n, NullMeasurableSet (P n) MeasureTheory.volume)
    (h_div : ¬ Summable (fun n => cmodulus (P n \ P (n + 1)))) :
    (⋂ n, P n) = {0} := by
  exact groetzsch_criterion h_nested h_zero h_conn h_meas h_div

end Quadratic
end MLC
