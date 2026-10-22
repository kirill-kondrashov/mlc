import Mlc.Quadratic.Complex.YoccozConformal
import Mlc.Quadratic.Complex.ConformalGroetzsch
import Mlc.ParaPuzzleConnectivity

/-!
# Regression facts for the frozen model

These theorems record two independent reasons the current frozen
Green-sublevel/renormalization interfaces cannot serve as a shrinking
Yoccoz tower: the imported `modulus` is Gaussian weighted area, and the
frozen Green tower has a non-singleton intersection at every Mandelbrot
parameter.
-/

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace MLC
namespace ModelRegression

open Quadratic

/-- The repository's Gaussian weighted-area annuli are always summable. -/
theorem weighted_puzzleAnnuli_summable (c : Complex) :
    Summable (fun n => modulus (PuzzleAnnulus c n)) := by
  apply summable_of_sum_range_le
    (c := modulus Set.univ) (fun n => modulus_nonneg _)
  intro N
  have hmeas : ∀ n, MeasurableSet (PuzzleAnnulus c n) := by
    intro n
    exact (isOpen_dynamicalPuzzlePiece_conformal c n).measurableSet.diff
      (isOpen_dynamicalPuzzlePiece_conformal c (n + 1)).measurableSet
  have hdisj : Set.PairwiseDisjoint (Finset.range N) (PuzzleAnnulus c) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hzi hzj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hzi.2
        (subset_of_le_nested (P := fun n => DynamicalPuzzlePiece c n 0)
          (dynamical_puzzle_piece_nested c)
          (Nat.succ_le_of_lt hlt) hzj.1)
    · exact hzj.2
        (subset_of_le_nested (P := fun n => DynamicalPuzzlePiece c n 0)
          (dynamical_puzzle_piece_nested c)
          (Nat.succ_le_of_lt hgt) hzi.1)
  rw [← modulus_finset_sum hdisj (fun n _ => hmeas n)]
  unfold modulus
  apply integral_mono_measure (Measure.restrict_mono (Set.subset_univ _) le_rfl)
  · exact ae_restrict_of_ae (ae_of_all _ (fun z => le_of_lt (Real.exp_pos _)))
  · exact weight_integrable.integrableOn

/-- Every filled Julia set at a Mandelbrot parameter contains a nonzero point. -/
theorem exists_nonzero_filledJulia (c : Complex) (hc : c ∈ MandelbrotSet) :
    ∃ z ∈ K c, z ≠ 0 := by
  by_cases hc0 : c = 0
  · subst c
    refine ⟨1, ?_, one_ne_zero⟩
    change boundedOrbit 0 1
    refine ⟨1, fun n => ?_⟩
    have hfixed : orbit 0 1 n = 1 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [orbit_succ, fc, ih]
    rw [hfixed]
    norm_num
  · refine ⟨c, ?_, hc0⟩
    apply (green_function_eq_zero_iff_mem_K c c).mp
    have hz := (green_function_eq_zero_iff_mem_K c 0).mpr hc
    simpa [fc, hz] using green_function_functional_eq c 0

/-- The frozen translated Green-sublevel tower cannot shrink to its center. -/
theorem frozen_tower_ne_singleton (c : Complex) (hc : c ∈ MandelbrotSet) :
    (⋂ n, {p | green_function c (p - c) < (1 / 2 : Real) ^ n}) ≠ {c} := by
  rw [iInter_green_sublevel_translate_eq_translate_filledJulia]
  intro h
  obtain ⟨z, hz, hzne⟩ := exists_nonzero_filledJulia c hc
  have hmem : z + c ∈ (fun w => w + c) '' K c := ⟨z, hz, rfl⟩
  rw [h] at hmem
  have heq : z + c = 0 + c := by
    simpa only [zero_add] using (mem_singleton_iff.mp hmem)
  exact hzne (add_right_cancel heq)

/-- The current translated para-puzzle pieces have the same obstruction. -/
theorem paraPuzzle_tower_ne_singleton (c : Complex) (hc : c ∈ MandelbrotSet) :
    (⋂ n, ParaPuzzlePieceAt c n) ≠ {c} := by
  simpa only [paraPuzzlePieceAt_eq_green_translate hc] using
    frozen_tower_ne_singleton c hc

#print axioms weighted_puzzleAnnuli_summable
#print axioms frozen_tower_ne_singleton
#print axioms paraPuzzle_tower_ne_singleton

end ModelRegression
end MLC
