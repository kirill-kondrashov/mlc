import Yoccoz.Quadratic.Complex.Groetzsch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MLC
namespace Quadratic

open MeasureTheory BigOperators Set

noncomputable def cmodulus := modulus

theorem cmodulus_finset_sum {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {A : ι → Set ℂ}
    (h_disj : PairwiseDisjoint s A)
    (h_meas : ∀ i ∈ s, NullMeasurableSet (A i) volume) :
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
    · apply Disjoint.aedisjoint
      rw [Set.disjoint_right]
      intro z h_union h_i
      simp only [Set.mem_iUnion] at h_union
      rcases h_union with ⟨j, hj_s, h_z_j⟩
      have h_neq : i ≠ j := ne_comm.mp (ne_of_mem_of_not_mem hj_s hi)
      have h_disj_ij :=
        h_disj (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj_s) h_neq
      exact Set.disjoint_left.1 h_disj_ij h_i h_z_j
    · apply NullMeasurableSet.biUnion s.finite_toSet.countable
      intro j hj
      exact h_meas j (Finset.mem_insert_of_mem hj)
    · exact weight_integrable.integrableOn
    · exact weight_integrable.integrableOn

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
