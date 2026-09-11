import Mlc.CategoricalMandelbrot

/-!
# Finite combinatorial outer approximations

The finite combinatorial content is represented by a finite family of compact
cells at each resolution.  The fields of `FiniteCellOuterApproximation` are
the exact certificates that a concrete interval, cubical, or CAD
implementation must check.  The limit theorem below is proved from those
certificates and does not introduce an axiom.
-/

namespace MLC
namespace CertifiedOrbit

open Set Metric

noncomputable section

def dyadicRadius (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n

lemma dyadicRadius_pos (n : ℕ) : 0 < dyadicRadius n := by
  dsimp [dyadicRadius]
  positivity

lemma exists_dyadicRadius_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n, dyadicRadius n < ε := by
  exact exists_pow_lt_of_lt_one hε (by norm_num)

/-- A finite family of compact cells selected from the exact finite-orbit
    outer stages.  A concrete implementation supplies the index types and
    proves the displayed certificate fields. -/
structure FiniteCellOuterApproximation where
  index : ℕ → Type
  finite_index : ∀ n, Finite (index n)
  cell : ∀ n, index n → Set ℂ
  cell_nonempty : ∀ n i, (cell n i).Nonempty
  cell_compact : ∀ n i, IsCompact (cell n i)
  stage_antitone :
    ∀ {n m}, n ≤ m →
      (⋃ i, cell m i) ⊆ (⋃ i, cell n i)
  mandelbrot_subset_stage :
    ∀ n, MLC.Categorical.Mandelbrot.set ⊆ ⋃ i, cell n i
  cell_near_outer :
    ∀ n i x, x ∈ cell n i →
      ∃ y ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n,
        dist x y ≤ dyadicRadius n

def stage (A : FiniteCellOuterApproximation) (n : ℕ) : Set ℂ :=
  ⋃ i, A.cell n i

theorem stage_antitone (A : FiniteCellOuterApproximation)
    {n m : ℕ} (h : n ≤ m) :
    stage A m ⊆ stage A n :=
  A.stage_antitone h

theorem mandelbrot_subset_stage (A : FiniteCellOuterApproximation) (n : ℕ) :
    MLC.Categorical.Mandelbrot.set ⊆ stage A n :=
  A.mandelbrot_subset_stage n

theorem isCompact_stage (A : FiniteCellOuterApproximation) (n : ℕ) :
    IsCompact (stage A n) := by
  letI := A.finite_index n
  exact isCompact_iUnion (fun i => A.cell_compact n i)

theorem stage_subset_outerNeighborhood (A : FiniteCellOuterApproximation)
    (n : ℕ) :
    stage A n ⊆
      {x | ∃ y ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n,
        dist x y ≤ dyadicRadius n} := by
  intro x hx
  rcases mem_iUnion.mp hx with ⟨i, hxi⟩
  exact A.cell_near_outer n i x hxi

theorem iInter_stage_eq_mandelbrot (A : FiniteCellOuterApproximation) :
    (⋂ n, stage A n) = MLC.Categorical.Mandelbrot.set := by
  apply Subset.antisymm
  · intro x hx
    rw [← MLC.Categorical.Mandelbrot.iInter_outerOrbitSet_eq_set]
    refine mem_iInter.mpr ?_
    intro k
    apply (MLC.Categorical.Mandelbrot.isClosed_outerOrbitSet k).closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_dyadicRadius_lt hε
    let n := max k m
    have hkn : k ≤ n := Nat.le_max_left _ _
    have hmn : m ≤ n := Nat.le_max_right _ _
    have hpow : dyadicRadius n ≤ dyadicRadius m := by
      dsimp [dyadicRadius]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
    have hradius : dyadicRadius n < ε := lt_of_le_of_lt hpow hm
    have hxn : x ∈ stage A n := mem_iInter.mp hx n
    rcases mem_iUnion.mp hxn with ⟨i, hxi⟩
    obtain ⟨y, hy, hxy⟩ := A.cell_near_outer n i x hxi
    refine ⟨y, ?_, ?_⟩
    · exact MLC.Categorical.Mandelbrot.outerOrbitSet_antitone hkn hy
    · exact lt_of_le_of_lt hxy hradius
  · exact subset_iInter (fun n => mandelbrot_subset_stage A n)

theorem stage_nested_compact (A : FiniteCellOuterApproximation) :
    (∀ n, IsCompact (stage A n)) ∧
      (∀ {n m}, n ≤ m → stage A m ⊆ stage A n) := by
  exact ⟨isCompact_stage A, A.stage_antitone⟩

/-! ## A verified baseline instance

The one-cell instance below is intentionally not a fine combinatorial
discretization: it records the exact finite-orbit outer stages already present
in the repository.  Any cubical or CAD implementation can be compared with
this baseline by proving the same certificate fields. -/

def exactOrbitOuterApproximation :
    FiniteCellOuterApproximation where
  index := fun _ => Unit
  finite_index := fun _ => inferInstance
  cell := fun n _ => MLC.Categorical.Mandelbrot.outerOrbitSet n
  cell_nonempty := by
    intro n _
    exact ⟨0, by
      change ‖(0 : ℂ)‖ ≤ (2 : ℝ) ∧
        ∀ k ≤ n, ‖MLC.Quadratic.orbit 0 0 k‖ ≤ (2 : ℝ)
      refine ⟨by norm_num, ?_⟩
      have horbit :
          ∀ k, MLC.Quadratic.orbit (0 : ℂ) 0 k = 0 := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
            rw [MLC.Quadratic.orbit_succ, ih]
            simp [MLC.Quadratic.fc]
      intro k hk
      rw [horbit k]
      norm_num⟩
  cell_compact := by
    intro n _
    exact MLC.Categorical.Mandelbrot.isCompact_outerOrbitSet n
  stage_antitone := by
    intro n m h x hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    exact mem_iUnion.mpr ⟨i, MLC.Categorical.Mandelbrot.outerOrbitSet_antitone h hxi⟩
  mandelbrot_subset_stage := by
    intro n x hx
    exact mem_iUnion.mpr ⟨(), MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet n hx⟩
  cell_near_outer := by
    intro n _ x hx
    exact ⟨x, hx, by
      simp
      exact (dyadicRadius_pos n).le⟩

@[simp] theorem stage_exactOrbitOuterApproximation (n : ℕ) :
    stage exactOrbitOuterApproximation n =
      MLC.Categorical.Mandelbrot.outerOrbitSet n := by
  ext x
  constructor
  · intro hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    simpa using hxi
  · intro hx
    exact mem_iUnion.mpr ⟨(), hx⟩

end
end CertifiedOrbit
end MLC
