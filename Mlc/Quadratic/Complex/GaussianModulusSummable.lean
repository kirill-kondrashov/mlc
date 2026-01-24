import Yoccoz.Quadratic.Complex.Groetzsch
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.Green
import Mlc.Quadratic.Complex.PrincipalNestAnnulus

namespace MLC.Quadratic

open Complex Topology Set Filter MeasureTheory Classical

noncomputable section

/-!
Facts about the `Yoccoz` package's proxy `modulus`.

In `Yoccoz/Quadratic/Complex/Groetzsch.lean`, `modulus A` is defined as a weighted area integral
`∫ z in A, exp (-‖z‖^2)`. Since the weight is integrable on `ℂ`, the modulus of *every* set is
bounded above by the modulus of `univ`.

Consequently, for any pairwise disjoint family of sets, the series of their moduli is summable,
bounded by `modulus univ`. In particular, for any nested family `P n`, the annuli `P n \\ P (n+1)`
have summable moduli.

This means that the hypothesis `¬ Summable (fun n => modulus (P n \\ P (n+1)))` appearing in the
proxy "Grötzsch criterion" can never be discharged from geometric information alone: it requires a
different notion of modulus (e.g. the true conformal modulus).
-/

namespace GaussianModulus

def unionUpTo (A : ℕ → Set ℂ) (N : ℕ) : Set ℂ :=
  ⋃ n ∈ Finset.range N, A n

lemma unionUpTo_succ (A : ℕ → Set ℂ) (N : ℕ) :
    unionUpTo A (N + 1) = unionUpTo A N ∪ A N := by
  ext z
  constructor
  · intro hz
    rcases mem_iUnion.mp hz with ⟨n, hz⟩
    rcases mem_iUnion.mp hz with ⟨hn, hzn⟩
    have hn' : n < N + 1 := by simpa [Finset.mem_range] using hn
    have hn_le : n ≤ N := Nat.lt_succ_iff.mp hn'
    cases lt_or_eq_of_le hn_le with
    | inl hlt =>
        left
        refine mem_iUnion.mpr ?_
        refine ⟨n, mem_iUnion.mpr ?_⟩
        refine ⟨?_, hzn⟩
        simpa [Finset.mem_range] using hlt
    | inr heq =>
        right
        simpa [heq] using hzn
  · intro hz
    rcases hz with hz | hz
    · rcases mem_iUnion.mp hz with ⟨n, hz⟩
      rcases mem_iUnion.mp hz with ⟨hn, hzn⟩
      have hn' : n < N := by simpa [Finset.mem_range] using hn
      have hn'' : n < N + 1 := Nat.lt_trans hn' (Nat.lt_succ_self N)
      refine mem_iUnion.mpr ?_
      refine ⟨n, mem_iUnion.mpr ?_⟩
      refine ⟨?_, hzn⟩
      simpa [Finset.mem_range] using hn''
    · refine mem_iUnion.mpr ?_
      refine ⟨N, mem_iUnion.mpr ?_⟩
      refine ⟨?_, hz⟩
      simp [Finset.mem_range]

lemma unionUpTo_subset {A : ℕ → Set ℂ} {S : Set ℂ} (N : ℕ) (h_sub : ∀ n, A n ⊆ S) :
    unionUpTo A N ⊆ S := by
  intro z hz
  rcases mem_iUnion.mp hz with ⟨n, hz⟩
  rcases mem_iUnion.mp hz with ⟨hn, hz⟩
  exact h_sub n hz

lemma disjoint_unionUpTo_last {A : ℕ → Set ℂ} (N : ℕ)
    (h_disj : Pairwise fun i j => Disjoint (A i) (A j)) :
    Disjoint (unionUpTo A N) (A N) := by
  refine disjoint_left.2 ?_
  intro z hzU hzN
  rcases mem_iUnion.mp hzU with ⟨i, hzU⟩
  rcases mem_iUnion.mp hzU with ⟨hi, hzAi⟩
  have hi' : i < N := by simpa [unionUpTo, Finset.mem_range] using hi
  have hne : i ≠ N := Nat.ne_of_lt hi'
  exact (disjoint_left.1 (h_disj hne)) hzAi hzN

lemma modulus_unionUpTo_eq_sum (A : ℕ → Set ℂ)
    (h_disj : Pairwise fun i j => Disjoint (A i) (A j))
    (h_meas : ∀ n, NullMeasurableSet (A n) volume) :
    ∀ N, MLC.Quadratic.modulus (unionUpTo A N) =
      Finset.sum (Finset.range N) (fun n => MLC.Quadratic.modulus (A n)) := by
  intro N
  induction N with
  | zero =>
      simp [unionUpTo, MLC.Quadratic.modulus]
  | succ N ih =>
      have h_disjU : Disjoint (unionUpTo A N) (A N) := disjoint_unionUpTo_last (A := A) N h_disj
      -- `integral_union_ae` only needs `NullMeasurableSet` for the second set.
      have h_integral :
          MLC.Quadratic.modulus (unionUpTo A (N + 1)) =
            MLC.Quadratic.modulus (unionUpTo A N) + MLC.Quadratic.modulus (A N) := by
        simp [MLC.Quadratic.modulus, unionUpTo_succ, integral_union_ae,
          (Disjoint.aedisjoint h_disjU), h_meas N, MLC.Quadratic.weight_integrable.integrableOn]
      -- Turn the integral identity into the desired finite-sum identity.
      simp [Finset.sum_range_succ, ih, h_integral, add_comm]

theorem summable_modulus_of_pairwise_disjoint {A : ℕ → Set ℂ} {S : Set ℂ}
    (h_disj : Pairwise fun i j => Disjoint (A i) (A j))
    (h_sub : ∀ n, A n ⊆ S)
    (h_meas : ∀ n, NullMeasurableSet (A n) volume) :
    Summable (fun n => MLC.Quadratic.modulus (A n)) := by
  -- Bound finite partial sums by `modulus S`.
  have h_bounded : ∀ N,
      Finset.sum (Finset.range N) (fun n => MLC.Quadratic.modulus (A n))
        ≤ MLC.Quadratic.modulus S := by
    intro N
    have h_eq := (modulus_unionUpTo_eq_sum (A := A) h_disj h_meas N).symm
    -- Monotonicity of the integral for nonnegative integrands.
    have h_mono : MLC.Quadratic.modulus (unionUpTo A N) ≤ MLC.Quadratic.modulus S := by
      have hUS : unionUpTo A N ⊆ S := unionUpTo_subset (A := A) N h_sub
      unfold MLC.Quadratic.modulus
      apply integral_mono_measure (Measure.restrict_mono hUS le_rfl)
      · apply ae_restrict_of_ae
        apply ae_of_all
        intro z
        exact le_of_lt (Real.exp_pos _)
      · exact MLC.Quadratic.weight_integrable.integrableOn
    simpa [h_eq] using h_mono
  exact summable_of_sum_range_le (fun _ => MLC.Quadratic.modulus_nonneg _) h_bounded

end GaussianModulus

namespace PrincipalNest

open GaussianModulus

lemma isOpen_dynamicalPuzzlePiece (c : ℂ) (n : ℕ) :
    IsOpen (DynamicalPuzzlePiece c n 0) := by
  have h_base : IsOpen {w | green_function c w < (1 / 2) ^ n} :=
    IsOpen.preimage (continuous_green_function c) isOpen_Iio
  simpa [DynamicalPuzzlePiece] using IsOpen.connectedComponentIn h_base

lemma nullMeasurable_dynamicalPuzzlePiece (c : ℂ) (n : ℕ) :
    NullMeasurableSet (DynamicalPuzzlePiece c n 0) volume :=
  (isOpen_dynamicalPuzzlePiece c n).measurableSet.nullMeasurableSet

lemma nullMeasurable_dynAnnulus (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) :
    NullMeasurableSet (dynAnnulus c depths n) volume := by
  -- `dynAnnulus` is a difference of open (hence measurable) sets.
  have h1 : NullMeasurableSet (DynamicalPuzzlePiece c (depths n) 0) volume :=
    nullMeasurable_dynamicalPuzzlePiece c (depths n)
  have h2 : NullMeasurableSet (DynamicalPuzzlePiece c (depths (n + 1)) 0) volume :=
    nullMeasurable_dynamicalPuzzlePiece c (depths (n + 1))
  simpa [dynAnnulus] using h1.diff h2

lemma pairwise_disjoint_dynAnnulus (c : ℂ) (depths : ℕ → ℕ) (hmono : Monotone depths) :
    Pairwise fun i j => Disjoint (dynAnnulus c depths i) (dynAnnulus c depths j) := by
  classical
  intro i j hij
  -- Prove disjointness in the directed case `i < j`, then use symmetry for the other order.
  have disjoint_of_lt : ∀ {i j : ℕ}, i < j → Disjoint (dynAnnulus c depths i) (dynAnnulus c depths j) := by
    intro i j hlt
    refine disjoint_left.2 ?_
    intro z hzi hzj
    have hzi' : z ∉ DynamicalPuzzlePiece c (depths (i + 1)) 0 := hzi.2
    have hzj_in : z ∈ DynamicalPuzzlePiece c (depths j) 0 := hzj.1
    -- From monotonicity, `depths (i+1) ≤ depths j`, so the depth-`j` piece is contained in the
    -- depth-`(i+1)` piece (antitone in depth).
    have hle : depths (i + 1) ≤ depths j := by
      have : i + 1 ≤ j := Nat.succ_le_iff.2 hlt
      exact hmono this
    have hzj_in' : z ∈ DynamicalPuzzlePiece c (depths (i + 1)) 0 :=
      (PrincipalNest.antitone_dynamicalPuzzlePiece c hle) hzj_in
    exact hzi' hzj_in'
  cases lt_or_gt_of_ne hij with
  | inl hlt => exact disjoint_of_lt hlt
  | inr hgt => exact (disjoint_of_lt hgt).symm

theorem summable_modulus_dynAnnulus (c : ℂ) (depths : ℕ → ℕ) (hmono : Monotone depths) :
    Summable (fun n => MLC.Quadratic.modulus (dynAnnulus c depths n)) := by
  classical
  refine GaussianModulus.summable_modulus_of_pairwise_disjoint
      (A := fun n => dynAnnulus c depths n) (S := (Set.univ : Set ℂ)) ?_ ?_ ?_
  · exact pairwise_disjoint_dynAnnulus (c := c) (depths := depths) hmono
  · intro n z hz
    trivial
  · intro n
    exact nullMeasurable_dynAnnulus (c := c) (depths := depths) n

end PrincipalNest

end
end MLC.Quadratic
