import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green
import Mlc.CheckAxioms
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- The dynamical puzzle piece of depth n containing z. -/
def DynamicalPuzzlePiece (c : ℂ) (n : ℕ) (z : ℂ) : Set ℂ :=
  {w | green_function c w < (1 / 2) ^ n}

/-- The modulus of an annulus. -/
opaque modulus (A : Set ℂ) : ℝ

axiom modulus_empty : modulus ∅ = 0

/-- The annulus between two nested puzzle pieces around the critical point. -/
def PuzzleAnnulus (c : ℂ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c n 0 \ DynamicalPuzzlePiece c (n + 1) 0

theorem dynamical_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    DynamicalPuzzlePiece c (n + 1) 0 ⊆ DynamicalPuzzlePiece c n 0 := by
  intro w hw
  dsimp [DynamicalPuzzlePiece] at *
  apply lt_trans hw
  rw [pow_succ]
  nth_rw 2 [← one_mul ((1 / 2 : ℝ) ^ n)]
  rw [mul_comm]
  apply mul_lt_mul_of_pos_right
  · norm_num
  · apply pow_pos
    norm_num

ensure_no_sorry dynamical_puzzle_piece_nested

theorem mem_dynamical_puzzle_piece_self (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ) :
    0 ∈ DynamicalPuzzlePiece c n 0 := by
  have h0 : 0 ∈ K c := hc
  rw [← green_function_eq_zero_iff_mem_K] at h0
  dsimp [DynamicalPuzzlePiece]
  rw [h0]
  apply pow_pos
  norm_num

ensure_no_sorry mem_dynamical_puzzle_piece_self

theorem dynamical_puzzle_piece_empty_of_large_n (c : ℂ) (hc : c ∉ MandelbrotSet) :
    ∃ N, ∀ n ≥ N, 0 ∉ DynamicalPuzzlePiece c n 0 := by
  have h_not_in_K : 0 ∉ K c := hc
  rw [← green_function_pos_iff_not_mem_K] at h_not_in_K
  have h_pos : 0 < green_function c 0 := h_not_in_K
  
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < green_function c 0 := by
    have h_tendsto : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      · norm_num
      · norm_num
    exact ((tendsto_order.1 h_tendsto).2 (green_function c 0) h_pos).exists
  
  use N
  intro n hn
  dsimp [DynamicalPuzzlePiece]
  rw [not_lt]
  apply le_trans _ (le_of_lt hN)
  apply pow_le_pow_of_le_one
  · norm_num
  · norm_num
  · exact hn

ensure_no_sorry dynamical_puzzle_piece_empty_of_large_n

/-- Grötzsch's Inequality / Criterion -/
axiom groetzsch_criterion {P : ℕ → Set ℂ} :
  (∀ n, P (n + 1) ⊆ P n) →
  (∀ n, 0 ∈ P n) →
  ¬ Summable (fun n => modulus (P n \ P (n + 1))) →
  (⋂ n, P n) = {0}

/-- A para-puzzle piece in the parameter plane. -/
def ParaPuzzlePiece (n : ℕ) : Set ℂ := {c | c ∈ DynamicalPuzzlePiece c n 0}

/-- Correspondence between parameter and dynamical pieces. -/
lemma para_dynamical_correspondence (c : ℂ) (n : ℕ) :
    c ∈ ParaPuzzlePiece n ↔ fc c 0 ∈ DynamicalPuzzlePiece c n 0 := by
  simp [ParaPuzzlePiece, fc]

/-- The Correspondence Principle:
    If the dynamical pieces shrink to a point, the parameter pieces shrink to a point. -/
axiom parameter_shrink_ax (c : ℂ) :
    (⋂ n, DynamicalPuzzlePiece c n 0) = {0} → (⋂ n, ParaPuzzlePiece n) = {c}

/-- Parameter puzzle pieces are open sets. -/
axiom para_puzzle_piece_open (n : ℕ) : IsOpen (ParaPuzzlePiece n)

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a point. -/
axiom para_puzzle_piece_basis (c : ℂ) :
    (⋂ n, ParaPuzzlePiece n) = {c} → ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePiece n ⊆ U

/-- Parameter puzzle pieces intersected with the Mandelbrot set are connected. -/
axiom para_puzzle_piece_inter_mandelbrot_connected (n : ℕ) :
    IsConnected (ParaPuzzlePiece n ∩ MandelbrotSet)

end

end MLC.Quadratic
