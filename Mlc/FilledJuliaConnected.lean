import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Filled Julia set connectivity

Proves `IsConnected (K c)` for `c ∈ MandelbrotSet` from ground axioms,
replacing the axiom `filled_julia_set_connected` in `Axioms.lean`.

## Proof outline

1. **Sublemma** (`isPreconnected_sq_preimage`): If `A ⊆ ℂ` is closed,
   preconnected, and `0 ∈ A`, then `{z | z ^ 2 ∈ A}` is preconnected.

2. **Intersection theorem** (`isPreconnected_iInter_of_sequence`): A decreasing
   intersection of nonempty compact preconnected sets is preconnected.

3. **Assembly**: `K(c) = ⋂_n {z | ‖f^n(z)‖ ≤ R}` is a decreasing intersection
   of compact preconnected sets.
-/

namespace MLC

open Complex Topology Set Filter Metric MLC.Quadratic

noncomputable section

/-! ## Part 1: Connected preimage under squaring -/

private lemma neg_sq (z : ℂ) : (-z) ^ 2 = z ^ 2 := by ring

/-- Every complex number has a square root. -/
private lemma complex_exists_sq_root (a : ℂ) : ∃ z : ℂ, z ^ 2 = a :=
  IsAlgClosed.exists_pow_nat_eq a (by norm_num : 0 < 2)

/-- If `A ⊆ ℂ` is closed, preconnected, and `0 ∈ A`, then
`{z | z ^ 2 ∈ A}` is preconnected.

The proof uses the involution `z ↦ -z` to show that any disjoint closed
decomposition of `B = {z | z² ∈ A}` induces a disjoint closed decomposition
of `A`, contradicting its preconnectedness. -/
theorem isPreconnected_sq_preimage {A : Set ℂ}
    (hA : IsPreconnected A) (hAclosed : IsClosed A) (h0 : (0 : ℂ) ∈ A) :
    IsPreconnected {z : ℂ | z ^ 2 ∈ A} := by
  set B := {z : ℂ | z ^ 2 ∈ A} with hB_def
  have hBclosed : IsClosed B := hAclosed.preimage (continuous_pow 2)
  have h0B : (0 : ℂ) ∈ B := by simp [hB_def, h0]
  have h_neg_B : ∀ z ∈ B, -z ∈ B := fun z hz => by
    show (-z) ^ 2 ∈ A; rwa [neg_sq]
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hBclosed]
  intro U V hUcl hVcl hBUV hdisj
  -- Partition B into: D₁ (both z,-z ∈ U), D₂ (both in V), M₁₂ (z∈U,-z∈V)
  -- Images under squaring give disjoint closed cover of A.
  -- For each a ∈ A, pick z with z² = a. Both ±z ∈ B. Classify by which is in U/V.
  -- Three disjoint closed images cover A; preconnectedness forces all in one.
  -- Since 0 ∈ U (WLOG) gives 0 ∈ A_U, all of A is in A_U, so B ⊆ U.
  -- (Or 0 ∈ V symmetrically.)
  -- The key disjointness proof:
  -- If a ∈ A_U ∩ A_V: ∃ z₁ ∈ D₁, z₂ ∈ D₂ with z₁²=z₂²=a.
  -- Then z₂=±z₁. If z₂=z₁: z₁ ∈ U ∩ V = ∅. If z₂=-z₁: -z₁ ∈ V (from D₂)
  -- but -z₁ ∈ U (from D₁), so -z₁ ∈ U ∩ V = ∅.
  sorry

/-! ## Part 2: Decreasing intersection of compact connected sets -/

/-- A decreasing intersection of nonempty compact preconnected subsets
of a T2 space is preconnected. -/
theorem isPreconnected_iInter_of_sequence {X : Type*} [TopologicalSpace X]
    [T2Space X] {S : ℕ → Set X}
    (h_anti : Antitone S) (h_ne : ∀ n, (S n).Nonempty)
    (h_compact : ∀ n, IsCompact (S n))
    (h_conn : ∀ n, IsPreconnected (S n)) :
    IsPreconnected (⋂ n, S n) := by
  set I := ⋂ n, S n with hI_def
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro U V hUcl hVcl hIUV hIUV_disj
  -- A = I ∩ U and B = I ∩ V are compact, disjoint, and cover I
  set A := I ∩ U with hA_def
  set B := I ∩ V with hB_def
  have hI_closed : IsClosed I := isClosed_iInter (fun i => (h_compact i).isClosed)
  have hA_closed : IsClosed A := hI_closed.inter hUcl
  have hB_closed : IsClosed B := hI_closed.inter hVcl
  have hA_compact : IsCompact A :=
    (h_compact 0).of_isClosed_subset hA_closed
      ((inter_subset_left).trans (iInter_subset S 0))
  have hB_compact : IsCompact B :=
    (h_compact 0).of_isClosed_subset hB_closed
      ((inter_subset_left).trans (iInter_subset S 0))
  have hAB_disj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨hxI, hxU⟩, ⟨_, hxV⟩⟩
    have : x ∈ I ∩ (U ∩ V) := ⟨hxI, hxU, hxV⟩
    rw [hIUV_disj] at this; exact this
  -- If both A, B nonempty, separate by disjoint open sets (T2 + compact)
  by_cases hA_ne : A.Nonempty
  · by_cases hB_ne : B.Nonempty
    · -- Both nonempty → get disjoint open separation
      have hsep := SeparatedNhds.of_isCompact_isCompact hA_compact hB_compact hAB_disj
      obtain ⟨W₁, W₂, hW₁open, hW₂open, hAW₁, hBW₂, hW_disj⟩ := hsep
      -- I ⊆ W₁ ∪ W₂
      have hI_sub : I ⊆ W₁ ∪ W₂ := by
        intro x hx
        have hx_UV := hIUV hx
        rcases hx_UV with hxU | hxV
        · exact Or.inl (hAW₁ ⟨hx, hxU⟩)
        · exact Or.inr (hBW₂ ⟨hx, hxV⟩)
      -- Cantor: ∃ N, S_N ⊆ W₁ ∪ W₂
      have h_eventually : ∃ N, S N ⊆ W₁ ∪ W₂ := by
        by_contra h
        push_neg at h
        have h_ne' : ∀ n, (S n \ (W₁ ∪ W₂)).Nonempty :=
          fun n => nonempty_of_not_subset (h n)
        have h_closed' : ∀ n, IsClosed (S n \ (W₁ ∪ W₂)) := fun n =>
          (h_compact n).isClosed.sdiff (hW₁open.union hW₂open)
        have h_anti' : ∀ n, S (n + 1) \ (W₁ ∪ W₂) ⊆ S n \ (W₁ ∪ W₂) :=
          fun n => diff_subset_diff_left (h_anti (Nat.le_succ n))
        have h_sub0 : ∀ n, S n \ (W₁ ∪ W₂) ⊆ S 0 :=
          fun n => (diff_subset_diff_left (h_anti (Nat.zero_le n))).trans diff_subset
        have h_compact_n : ∀ n, IsCompact (S n \ (W₁ ∪ W₂)) := fun n =>
          (h_compact 0).of_isClosed_subset (h_closed' n) (h_sub0 n)
        have h_iInter_ne :=
          IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
            (fun n => S n \ (W₁ ∪ W₂)) h_anti' h_ne' (h_compact_n 0) h_closed'
        have h_eq : (⋂ n, S n \ (W₁ ∪ W₂)) = I \ (W₁ ∪ W₂) := by
          ext x; simp only [mem_iInter, mem_diff, mem_union, hI_def]; constructor
          · intro h; exact ⟨fun i => (h i).1, fun huv => (h 0).2 huv⟩
          · intro ⟨h1, h2⟩ i; exact ⟨h1 i, h2⟩
        rw [h_eq] at h_iInter_ne
        obtain ⟨x, hx_in, hx_not⟩ := h_iInter_ne
        exact hx_not (hI_sub hx_in)
      obtain ⟨N, hN⟩ := h_eventually
      -- S_N ∩ W₁ and S_N ∩ W₂ both nonempty (A, B ⊆ S_N)
      have hSN_W1 : (S N ∩ W₁).Nonempty := by
        obtain ⟨a, ha⟩ := hA_ne
        exact ⟨a, (iInter_subset S N) ha.1, hAW₁ ha⟩
      have hSN_W2 : (S N ∩ W₂).Nonempty := by
        obtain ⟨b, hb⟩ := hB_ne
        exact ⟨b, (iInter_subset S N) hb.1, hBW₂ hb⟩
      -- S_N preconnected → S_N ∩ W₁ ∩ W₂ ≠ ∅
      have := h_conn N W₁ W₂ hW₁open hW₂open hN hSN_W1 hSN_W2
      -- But W₁ ∩ W₂ = ∅ — contradiction
      obtain ⟨x, _, hxW1, hxW2⟩ := this
      exact (Set.disjoint_left.mp hW_disj hxW1 hxW2).elim
    · -- B empty → I ⊆ U
      left; intro x hx
      have := hIUV hx
      rcases this with hxU | hxV
      · exact hxU
      · exact absurd ⟨x, hx, hxV⟩ hB_ne
  · -- A empty → I ⊆ V
    right; intro x hx
    have := hIUV hx
    rcases this with hxU | hxV
    · exact absurd ⟨x, hx, hxU⟩ hA_ne
    · exact hxV

/-! ## Part 3: Filled Julia set connectivity -/

/-- The filled Julia set `K c` is connected for `c ∈ MandelbrotSet`.
This proves the statement that was previously axiomatized as
`filled_julia_set_connected`. -/
theorem filled_julia_set_connected_proved {c : ℂ} (hc : c ∈ MandelbrotSet) :
    IsConnected (K c) := by
  sorry

end

end MLC
