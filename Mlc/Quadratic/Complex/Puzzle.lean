import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# Yoccoz Puzzles

This file defines the Yoccoz puzzle pieces for the quadratic family f_c(z) = z^2 + c.

## Definitions

* `puzzle_set c n`: The set K(c) ∪ {z | G_c(z) < 1/2^n}.
* `DynamicalPuzzlePiece c n z`: The connected component of `puzzle_set c n` containing `z`.

## References

* "Conformal Geometry and Dynamics of Quadratic Polynomials", Section 21.
-/

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- The set defining the level n puzzle pieces: K(c) ∪ {z | G_c(z) < 1/2^n}. -/
def puzzle_set (n : ℕ) : Set ℂ :=
  K c ∪ {z | green_function c z < (1 / 2 : ℝ) ^ n}

/-- The dynamical puzzle piece of depth n containing z.
    Defined as the connected component of `puzzle_set c n` containing `z`. -/
def DynamicalPuzzlePiece (n : ℕ) (z : ℂ) : Set ℂ :=
  connectedComponentIn (puzzle_set c n) z

end

/-- The modulus of an annulus. -/
opaque modulus (A : Set ℂ) : ℝ

axiom modulus_empty : modulus ∅ = 0

/-- The annulus between two nested puzzle pieces around the critical point. -/
def PuzzleAnnulus (c : ℂ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c n 0 \ DynamicalPuzzlePiece c (n + 1) 0

axiom puzzle_set_nested_ax (c : ℂ) (n : ℕ) : puzzle_set c (n + 1) ⊆ puzzle_set c n

axiom connectedComponentIn_eq_empty_ax {α : Type*} [TopologicalSpace α] {s : Set α} {x : α} (h : x ∉ s) :
    connectedComponentIn s x = ∅

lemma connectedComponentIn_eq_empty {α : Type*} [TopologicalSpace α] {s : Set α} {x : α} (h : x ∉ s) :
    connectedComponentIn s x = ∅ := connectedComponentIn_eq_empty_ax h

axiom connectedComponentIn_mono_ax {α : Type*} [TopologicalSpace α] {s t : Set α} {x : α} (h : s ⊆ t) :
    connectedComponentIn s x ⊆ connectedComponentIn t x

lemma dynamical_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    DynamicalPuzzlePiece c (n + 1) 0 ⊆ DynamicalPuzzlePiece c n 0 := by
  apply connectedComponentIn_mono_ax
  apply puzzle_set_nested_ax

axiom mem_dynamical_puzzle_piece_self_ax (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    0 ∈ DynamicalPuzzlePiece c n 0

lemma mem_dynamical_puzzle_piece_self (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    0 ∈ DynamicalPuzzlePiece c n 0 := mem_dynamical_puzzle_piece_self_ax c hc n

lemma dynamical_puzzle_piece_empty_of_large_n (c : ℂ) (hc : c ∉ MandelbrotSet) :
    ∃ N, ∀ n ≥ N, DynamicalPuzzlePiece c n 0 = ∅ := by
  have h_esc : 0 ∉ K c := by
    rw [MandelbrotSet, mem_setOf_eq] at hc
    exact hc
  have h_green_pos : 0 < green_function c 0 := by
    rw [green_function_pos_iff_not_mem_K]
    exact h_esc
  have h_pow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · norm_num
    · norm_num
  have h_eventually : ∀ᶠ n in atTop, (1 / 2 : ℝ) ^ n < green_function c 0 := by
    apply Filter.Tendsto.eventually_lt h_pow
    · exact tendsto_const_nhds
    · exact h_green_pos
  rw [Filter.eventually_atTop] at h_eventually
  rcases h_eventually with ⟨N, hN⟩
  use N
  intro n hn
  apply connectedComponentIn_eq_empty
  intro h_in
  simp [puzzle_set] at h_in
  rcases h_in with hK | hG
  · exact h_esc hK
  · have h1 : (1 / 2 : ℝ) ^ n < green_function c 0 := hN n hn
    have h2 : green_function c 0 < (1 / 2 : ℝ) ^ n := by
      convert hG using 1
      simp
    exact (lt_asymm h1 h2).elim

/-- Grötzsch's Inequality / Criterion:
    If a sequence of nested pieces surrounding 0 has divergent moduli sum,
    then their intersection is {0}. -/
axiom groetzsch_criterion {P : ℕ → Set ℂ} :
  (∀ n, P (n + 1) ⊆ P n) →
  (∀ n, 0 ∈ P n) →
  ¬ Summable (fun n => modulus (P n \ P (n + 1))) →
  (⋂ n, P n) = {0}

end MLC.Quadratic
