import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Yoccoz.Quadratic.Complex.Escape
import Yoccoz.Quadratic.Complex.Groetzsch
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace MLC

namespace Quadratic

open Complex Topology Filter Set MeasureTheory

noncomputable section

/-!
Yoccoz theorem using conformal modulus.

This is the classical direction used in the MLC strategy:
divergence of annulus moduli implies the critical puzzle pieces shrink to `{0}`.

We prove it from `groetzsch_criterion` (for parameters in `MandelbrotSet`) plus the escape
argument (for parameters outside `MandelbrotSet`).
-/

lemma isOpen_dynamicalPuzzlePiece_conformal (c : ℂ) (n : ℕ) :
    IsOpen (DynamicalPuzzlePiece c n 0) := by
  have h_base : IsOpen {w | green_function c w < (1 / 2) ^ n} :=
    IsOpen.preimage (continuous_green_function c) isOpen_Iio
  simpa [DynamicalPuzzlePiece] using IsOpen.connectedComponentIn h_base

theorem yoccoz_theorem_conformal (c : ℂ) :
    ¬ Summable (fun n => modulus (PuzzleAnnulus c n)) →
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} := by
  intro h_div
  by_cases hc : c ∈ MandelbrotSet
  · -- In `M`, apply Grötzsch criterion to the nested family `P n = DPP c n 0`.
    have h_nested : ∀ n, DynamicalPuzzlePiece c (n + 1) 0 ⊆ DynamicalPuzzlePiece c n 0 := by
      intro n
      exact dynamical_puzzle_piece_nested c n
    have h_zero : ∀ n, 0 ∈ DynamicalPuzzlePiece c n 0 := by
      intro n
      exact mem_dynamical_puzzle_piece_self c hc n
    have h_conn : ∀ n, IsConnected (DynamicalPuzzlePiece c n 0) := by
      intro n
      have h_ne : (DynamicalPuzzlePiece c n 0).Nonempty :=
        ⟨0, mem_dynamical_puzzle_piece_self c hc n⟩
      refine ⟨h_ne, ?_⟩
      rw [DynamicalPuzzlePiece] at h_ne ⊢
      exact isPreconnected_connectedComponentIn
    have h_meas : ∀ n, NullMeasurableSet (DynamicalPuzzlePiece c n 0) volume := by
      intro n
      exact (isOpen_dynamicalPuzzlePiece_conformal c n).measurableSet.nullMeasurableSet
    -- Rewrite the annuli as `PuzzleAnnulus`.
    have h_div' : ¬ Summable
        (fun n => modulus (DynamicalPuzzlePiece c n 0 \ DynamicalPuzzlePiece c (n + 1) 0)) := by
      exact h_div
    exact groetzsch_criterion (P := fun n => DynamicalPuzzlePiece c n 0)
      h_nested h_zero h_conn h_meas h_div'
  · -- Outside `M`, puzzle pieces eventually become empty, hence the moduli are summable.
    exfalso
    apply h_div
    rcases dynamical_puzzle_piece_empty_of_large_n c hc with ⟨N, hN⟩
    -- Finite-support argument: beyond `N`, the annuli are empty, hence have modulus `0`.
    refine summable_of_finite_support ?_
    have h_support : (Function.support fun n ↦ modulus (PuzzleAnnulus c n)) ⊆ Iio N := by
      intro n hn
      rw [Function.mem_support, ne_eq] at hn
      by_contra h_ge
      have h_ge' : n ≥ N := by simpa using (le_of_not_gt h_ge)
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
          exact hN n h_ge' h0
        rw [h_empty]
        simp [modulus_empty]
      exact hn this
    exact Set.Finite.subset (Set.finite_Iio N) h_support

end

end Quadratic

end MLC
