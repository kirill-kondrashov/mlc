import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green
import Mlc.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean

namespace MLC

open Quadratic Complex Topology Set Filter BigOperators Classical

section GroetzschLemmas

/-- Grötzsch's Inequality. -/
theorem groetzsch_inequality {A B S : Set ℂ} (h_disj : Disjoint A B) (h_sub : A ∪ B ⊆ S) :
    modulus A + modulus B ≤ modulus S := by
  apply groetzsch_inequality_axiom h_disj h_sub

lemma subset_of_le_nested {P : ℕ → Set ℂ} (h_nested : ∀ n, P (n + 1) ⊆ P n)
    {i j : ℕ} (hij : i ≤ j) : P j ⊆ P i := by
  have h_diff : ∃ k, j = i + k := Nat.exists_eq_add_of_le hij
  obtain ⟨k, rfl⟩ := h_diff
  clear hij
  induction k with
  | zero => exact subset_refl _
  | succ m ih =>
    rw [Nat.add_succ]
    apply subset_trans (h_nested (i + m)) ih

theorem modulus_summable_of_nontrivial_intersection {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (_h_conn : ∀ n, IsConnected (P n))
    (_h_nontriv : Set.Nontrivial (⋂ n, P n)) :
    Summable (fun n => modulus (P n \ P (n + 1))) := by
  let A := fun n => P n \ P (n + 1)
  have h_disj : ∀ i j, i < j → Disjoint (A i) (A j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    simp [A] at hi hj
    have h_sub : P j ⊆ P (i + 1) := subset_of_le_nested h_nested hij
    have z_in_P_j := hj.1
    have z_in_P_i_1 := h_sub z_in_P_j
    have z_not_in_P_i_1 := hi.2
    contradiction

  have h_union_sub : ∀ N, (⋃ n ∈ Finset.range N, A n) ⊆ P 0 \ P N := by
    intro N
    rw [Set.subset_def]
    intro z hz
    simp at hz
    obtain ⟨n, hn_lt, hn_z⟩ := hz
    simp [A] at hn_z
    constructor
    · -- z ∈ P 0
      have h_sub : P n ⊆ P 0 := subset_of_le_nested h_nested (Nat.zero_le n)
      exact h_sub hn_z.1
    · -- z ∉ P N
      intro h_in_N
      have h_sub : P N ⊆ P (n + 1) := subset_of_le_nested h_nested hn_lt
      apply hn_z.2
      apply h_sub h_in_N

  -- Monotonicity lemma
  have modulus_mono : ∀ {U V : Set ℂ}, U ⊆ V → modulus U ≤ modulus V := by
    intro U V h_sub
    have h_union : U ∪ ∅ ⊆ V := by simp [h_sub]
    have h_disj_empty : Disjoint U ∅ := disjoint_empty U
    have h_ineq := groetzsch_inequality (A := U) (B := ∅) (S := V) h_disj_empty h_union
    rw [modulus_empty, add_zero] at h_ineq
    exact h_ineq

  -- Bounded partial sums
  have h_bounded : ∀ N, Finset.sum (Finset.range N) (fun n => modulus (A n)) ≤ modulus (P 0 \ (⋂ n, P n)) := by
    intro N
    -- First show sum ≤ modulus (P 0 \ P N)
    have h_sum_le : Finset.sum (Finset.range N) (fun n => modulus (A n)) ≤ modulus (P 0 \ P N) := by
      induction N with
      | zero =>
        simp
        rw [modulus_empty]
      | succ k ih =>
        rw [Finset.sum_range_succ]
        have h_split : P 0 \ P (k + 1) = (P 0 \ P k) ∪ (P k \ P (k + 1)) := by
          ext z
          simp
          constructor
          · intro h
            by_cases hk : z ∈ P k
            · right; exact ⟨hk, h.2⟩
            · left; exact ⟨h.1, hk⟩
          · intro h
            cases h with
            | inl h => exact ⟨h.1, fun h_in => h.2 (h_nested k h_in)⟩
            | inr h =>
                have h_sub : P k ⊆ P 0 := subset_of_le_nested h_nested (Nat.zero_le k)
                exact ⟨h_sub h.1, h.2⟩

        have h_disj_split : Disjoint (P 0 \ P k) (P k \ P (k + 1)) := by
          rw [Set.disjoint_left]
          intro z h1 h2
          have h_in_Pk := h2.1
          have h_not_in_Pk := h1.2
          contradiction

        have h_ineq := groetzsch_inequality (A := P 0 \ P k) (B := P k \ P (k + 1)) (S := P 0 \ P (k + 1)) h_disj_split (subset_of_eq h_split.symm)
        apply le_trans (add_le_add ih (le_refl (modulus (A k))))
        exact h_ineq

    apply le_trans h_sum_le
    apply modulus_mono
    apply diff_subset_diff_right
    apply sInter_subset_of_mem
    simp

  apply summable_of_sum_range_le (fun n => modulus_nonneg _) h_bounded

theorem groetzsch_criterion {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (h_zero : ∀ n, 0 ∈ P n)
    (h_conn : ∀ n, IsConnected (P n))
    (h_div : ¬ Summable (fun n => modulus (P n \ P (n + 1)))) :
    (⋂ n, P n) = {0} := by
  by_contra h_neq
  have h_nontriv : Set.Nontrivial (⋂ n, P n) := by
    have h_0 : 0 ∈ ⋂ n, P n := Set.mem_iInter.mpr h_zero
    rw [Set.nontrivial_iff_exists_ne h_0]
    by_contra h_all_eq
    apply h_neq
    ext z
    constructor
    · intro hz
      by_cases h_z_eq : z = 0
      · rw [h_z_eq]; exact Set.mem_singleton 0
      · push_neg at h_all_eq
        specialize h_all_eq z hz
        contradiction
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact h_0
  have h_sum := modulus_summable_of_nontrivial_intersection h_nested h_conn h_nontriv
  contradiction

end GroetzschLemmas

section Combinatorics

/-- Non-renormalizable parameters.
    For the purpose of this plan, we define non-renormalizable parameters
    as those for which the Yoccoz puzzle moduli diverge.
    The deep work is then in the dichotomy axiom. -/
def NonRenormalizable (c : ℂ) : Prop :=
    ¬ Summable (fun n => modulus (PuzzleAnnulus c n))

/-- Non-renormalizable parameters have divergent moduli. -/
theorem non_renormalizable_moduli_diverge (c : ℂ) (h : NonRenormalizable c) :
    ¬ (Summable fun n => modulus (PuzzleAnnulus c n)) := h

end Combinatorics

section YoccozTheorem

/-- Yoccoz's Theorem: Divergence of moduli implies point intersection.
    Proof idea:
    *   If `c ∈ M`: We apply **Grötzsch's criterion** to the nested sequence of dynamical puzzle pieces.
        These pieces contain 0 and are connected. The divergence of the moduli of the annuli between
        them forces the intersection of the pieces to be a single point `{0}`.
    *   If `c ∉ M`: The orbit of 0 escapes. For large enough `n`, the potential level `1/2^n`
        is smaller than `G(0)`, so `0` is no longer in the puzzle piece (which is defined by `G(z) < 1/2^n`).
        Thus, the puzzle pieces eventually become empty. This would imply the sum of moduli is finite
        (sum of zeros), contradicting the divergence hypothesis. Thus, this case is impossible under
        the assumption of divergence. -/
theorem yoccoz_theorem (c : ℂ) :
    ¬ (Summable fun n => modulus (PuzzleAnnulus c n)) →
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} := by
  intro h_div
  by_cases hc : c ∈ MandelbrotSet
  · apply groetzsch_criterion
    · intro n
      apply dynamical_puzzle_piece_nested
    · intro n
      apply mem_dynamical_puzzle_piece_self c hc
    · intro n
      have h_ne : (DynamicalPuzzlePiece c n 0).Nonempty := ⟨0, mem_dynamical_puzzle_piece_self c hc n⟩
      rw [DynamicalPuzzlePiece] at h_ne ⊢
      exact ⟨h_ne, isPreconnected_connectedComponentIn⟩
    · exact h_div
  · exfalso
    apply h_div
    rcases dynamical_puzzle_piece_empty_of_large_n c hc with ⟨N, hN⟩
    apply summable_of_finite_support
    have : (Function.support fun n ↦ modulus (PuzzleAnnulus c n)) ⊆ Iio N := by
      intro n hn
      rw [Function.mem_support, ne_eq] at hn
      by_contra h_ge
      simp at h_ge
      have : modulus (PuzzleAnnulus c n) = 0 := by
        rw [PuzzleAnnulus]
        have h_empty : DynamicalPuzzlePiece c n 0 = ∅ := by
          ext x
          simp
          intro hx
          have h0 : 0 ∈ DynamicalPuzzlePiece c n 0 := by
            rw [DynamicalPuzzlePiece] at hx ⊢
            apply mem_connectedComponentIn
            exact connectedComponentIn_nonempty_iff.1 ⟨x, hx⟩
          exact hN n h_ge h0
        rw [h_empty]
        simp
        exact modulus_empty
      contradiction
    exact Set.Finite.subset (Set.finite_Iio N) this

end YoccozTheorem

end MLC
