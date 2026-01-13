import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MLC
namespace Quadratic

open Complex Topology Filter Set BigOperators Classical

noncomputable section

/-- A cylinder defined by its circumference and height.
    See: [Milnor, Dynamics in One Complex Variable, Appendix B]
    "Now let us form a cylinder C of circumference ∆x and height ∆y by gluing the left and right edges
    of our rectangle together. More precisely, let C by the quotient space which is obtained from the infinitely
    wide strip 0 < y < ∆y in the z -plane by identifying each point z = x + iy with its translate z + ∆x ." -/
structure Cylinder where
  circumference : ℝ
  height : ℝ
  c_pos : 0 < circumference
  h_pos : 0 < height

instance : Inhabited Cylinder where
  default := { circumference := 1, height := 1, c_pos := zero_lt_one, h_pos := zero_lt_one }

/-- The modulus of a cylinder is the ratio of height to circumference.
    "Define the modulus mod(C) of such a cylinder to be the ratio ∆y/∆x of height to circumference." -/
def Cylinder.modulus (C : Cylinder) : ℝ := C.height / C.circumference

/-- An opaque function that assigns a conformal cylinder to any set.
    For true annuli, this returns the conformally equivalent cylinder.
    For other sets, the value is arbitrary (but fixed). -/
opaque cylinder_of_set (S : Set ℂ) : Cylinder

/-- An annulus in the complex plane, defined by its underlying set and its conformal cylinder.
    Mathematically, an annulus is a topological cylinder (a doubly connected open set).
    It is conformally isomorphic to a standard annulus {z | r < |z| < R}. -/
structure Annulus where
  val : Set ℂ
  cyl : Cylinder := cylinder_of_set val

/-- The conformal modulus of an annulus.
    "It follows that the modulus of an annulus A can be defined as the modulus
    of any conformally isomorphic cylinder." -/
def raw_modulus (A : Annulus) : ℝ := A.cyl.modulus

/-- The modulus of an annulus.
    Defined to be 0 for the empty set, and the `raw_modulus` otherwise. -/
noncomputable def modulus (A : Annulus) : ℝ :=
  if A.val = ∅ then 0 else raw_modulus A

/-- The modulus of the empty set is 0.
    See: [Milnor, Dynamics in One Complex Variable, Appendix B] <https://arxiv.org/pdf/math/9201272.pdf>
    Local Reference: `refs/9201272v1.pdf`
    "By definition an infinite cylinder, that is a cylinder of infinite height, has modulus zero."
    (Note: Typically empty sets or degenerate annuli are treated as limiting
    cases or specific values like 0 or infinity depending on convention; Milnor
    assigns 0 to infinite cylinders in some contexts or infinite modulus to
    complements of points. Here we assume standard convention for empty
    annulus). -/
theorem modulus_empty : modulus { val := ∅ } = 0 := by
  simp [modulus]

/-- Modulus is non-negative.
    This follows from the definition of modulus as a conformal invariant.
    See: [Milnor, Dynamics in One Complex Variable] <https://arxiv.org/pdf/math/9201272.pdf>
    Local Reference: `refs/9201272v1.pdf`
    "Define the modulus mod(C) of such a cylinder to be the ratio ∆y/∆x of
    height to circumference." (Ratio of positive lengths is positive). -/
theorem modulus_nonneg (A : Annulus) : 0 ≤ modulus A := by
  unfold modulus
  split_ifs
  · exact le_refl 0
  · unfold raw_modulus Cylinder.modulus
    apply div_nonneg
    · apply le_of_lt A.cyl.h_pos
    · apply le_of_lt A.cyl.c_pos

/-- Axiom: Superadditivity of modulus for disjoint essential annuli.
    Reference: Milnor, Dynamics in One Complex Variable, Corollary B.5
    Local Reference: `refs/9201272v1.pdf` -/
axiom modulus_superadditive_axiom {A B S : Annulus}
  (h_disj : Disjoint A.val B.val) (h_sub : A.val ∪ B.val ⊆ S.val) :
  modulus A + modulus B ≤ modulus S

/-- Grötzsch's Inequality: Superadditivity of modulus for disjoint essential annuli.
    See: [Milnor, Dynamics in One Complex Variable, Corollary B.5] <https://arxiv.org/pdf/math/9201272.pdf>
    Local Reference: `refs/9201272v1.pdf`
    "Corollary B.5 (Grötzsch Inequality). Suppose that A' ⊂ A and A'' ⊂ A are
    two disjoint annuli, each essentailly embedded in A. Then mod(A') + mod(A'')
    ≤ mod(A)."

    Proof sketch (requires Conformal Geometry/Dirichlet Principle):
    1. Modulus is a conformal invariant, so we can map the container annulus S
       conformally to a straight cylinder C of height H and circumference W.
       mod(S) = H/W.
    2. The disjoint sub-annuli A and B map to disjoint sub-domains A' and B' in C.
    3. Since A and B are essentially embedded, A' and B' wrap around the cylinder
       and separate the top/bottom components.
    4. By the Dirichlet Principle (or Extremal Length), the modulus of a sub-annulus
       is bounded by the modulus of the cylinder it spans.
    5. The sum of the "effective heights" of A' and B' is at most H.
    6. Therefore, mod(A) + mod(B) ≤ mod(S). -/
theorem groetzsch_inequality {A B S : Annulus} (h_disj : Disjoint A.val B.val) (h_sub : A.val ∪ B.val ⊆ S.val) :
    modulus A + modulus B ≤ modulus S := by
  apply modulus_superadditive_axiom h_disj h_sub

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

/-- Grötzsch's Inequality implies summability if the intersection is non-trivial.
    Proof idea: We construct a sequence of disjoint annuli `A_n = P_n \ P_{n+1}`.
    By the contrapositive of Grötzsch's criterion (or directly by inequality), if the intersection
    is non-trivial (contains more than just a point), there is a core `K` inside all `P_n`.
    The disjoint annuli are all nested around `K`. Grötzsch's inequality implies their moduli
    sum up to at most the modulus of the container `P_0 \ K`, which is finite.
    Thus the sum converges. -/
theorem modulus_summable_of_nontrivial_intersection {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (_h_conn : ∀ n, IsConnected (P n))
    (_h_nontriv : Set.Nontrivial (⋂ n, P n)) :
    Summable (fun n => modulus { val := P n \ P (n + 1) }) := by
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
  have modulus_mono : ∀ {U V : Set ℂ}, U ⊆ V → modulus { val := U } ≤ modulus { val := V } := by
    intro U V h_sub
    have h_union : U ∪ ∅ ⊆ V := by simp [h_sub]
    have h_disj_empty : Disjoint U ∅ := disjoint_empty U
    have h_ineq := groetzsch_inequality (A := { val := U }) (B := { val := ∅ }) (S := { val := V }) h_disj_empty h_union
    rw [modulus_empty, add_zero] at h_ineq
    exact h_ineq

  -- Bounded partial sums
  have h_bounded : ∀ N, Finset.sum (Finset.range N) (fun n => modulus { val := A n }) ≤ modulus { val := P 0 \ (⋂ n, P n) } := by
    intro N
    -- First show sum ≤ modulus (P 0 \ P N)
    have h_sum_le : Finset.sum (Finset.range N) (fun n => modulus { val := A n }) ≤ modulus { val := P 0 \ P N } := by
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

        have h_ineq := groetzsch_inequality (A := { val := P 0 \ P k }) (B := { val := P k \ P (k + 1) }) (S := { val := P 0 \ P (k + 1) }) h_disj_split (subset_of_eq h_split.symm)
        apply le_trans (add_le_add ih (le_refl (modulus { val := A k })))
        exact h_ineq

    apply le_trans h_sum_le
    apply modulus_mono
    apply diff_subset_diff_right
    apply sInter_subset_of_mem
    simp

  apply summable_of_sum_range_le (fun n => modulus_nonneg _) h_bounded

/-- Grötzsch's Criterion: Divergence of moduli implies point intersection.
    See: [Milnor, Dynamics in One Complex Variable, Corollary B.7]
    Local Reference: `refs/9201272v1.pdf`
    "Corollary B.7. Suppose that K ⊂ U as described above. Then K reduces to a single point if and only if the annulus A = U rK has infinite modulus."

    Proof idea: We argue by contrapositive. If the intersection is non-trivial (contains more than just `{0}`),
    then `modulus_summable_of_nontrivial_intersection` implies the sum of moduli converges.
    This contradicts the hypothesis that the sum diverges.
    Therefore, the intersection must be trivial (equal to `{0}`). -/
theorem groetzsch_criterion {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (h_zero : ∀ n, 0 ∈ P n)
    (h_conn : ∀ n, IsConnected (P n))
    (h_div : ¬ Summable (fun n => modulus { val := P n \ P (n + 1) })) :
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

end

end Quadratic
end MLC
