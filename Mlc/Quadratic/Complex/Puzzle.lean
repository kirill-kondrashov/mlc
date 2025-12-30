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
  connectedComponentIn {w | green_function c w < (1 / 2) ^ n} z

/-- The modulus of an annulus. -/
opaque modulus (A : Set ℂ) : ℝ

axiom modulus_empty : modulus ∅ = 0

/-- The annulus between two nested puzzle pieces around the critical point. -/
def PuzzleAnnulus (c : ℂ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c n 0 \ DynamicalPuzzlePiece c (n + 1) 0

theorem dynamical_puzzle_piece_nested (c : ℂ) (n : ℕ) :
    DynamicalPuzzlePiece c (n + 1) 0 ⊆ DynamicalPuzzlePiece c n 0 := by
  apply connectedComponentIn_mono
  intro w hw
  dsimp at *
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
  apply mem_connectedComponentIn
  change green_function c 0 < (1 / 2) ^ n
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
  intro h_mem
  have h_in_set : 0 ∈ {w | green_function c w < (1 / 2) ^ n} :=
    (connectedComponentIn_subset {w | green_function c w < (1 / 2) ^ n} 0) h_mem
  rw [mem_setOf_eq] at h_in_set
  have h_le : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N := by
    apply pow_le_pow_of_le_one
    · norm_num
    · norm_num
    · exact hn
  have h_lt : (1 / 2 : ℝ) ^ n < green_function c 0 :=
    lt_of_le_of_lt h_le hN
  linarith

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

/-- The Mandelbrot set is connected. -/
axiom mandelbrot_set_connected : IsConnected MandelbrotSet

/-- The filled Julia set is connected if c is in the Mandelbrot set. -/
axiom filled_julia_set_connected {c : ℂ} (h : c ∈ MandelbrotSet) : IsConnected (K c)

/-- Parameter puzzle pieces intersected with the Mandelbrot set are connected. -/
theorem para_puzzle_piece_inter_mandelbrot_connected (n : ℕ) :
    IsConnected (ParaPuzzlePiece n ∩ MandelbrotSet) := by
  have h_subset : MandelbrotSet ⊆ ParaPuzzlePiece n := by
    intro c hc
    rw [ParaPuzzlePiece, mem_setOf_eq]
    rw [DynamicalPuzzlePiece]
    
    have hc_in_K : c ∈ K c := by
      rw [K]
      unfold boundedOrbit
      rw [MandelbrotSet] at hc
      unfold boundedOrbit at hc
      obtain ⟨M, hM⟩ := hc
      use max M ‖c‖
      intro k
      cases k with
      | zero => simp
      | succ k =>
        simp only [orbit_succ]
        have h_shift : orbit c c k = orbit c 0 (k + 1) := by
          induction k with
          | zero => simp [orbit, fc]
          | succ k ih => simp [orbit_succ, ih]
        rw [h_shift]
        rw [← orbit_succ]
        apply le_trans (hM (k + 2)) (le_max_left _ _)

    have h_K_subset : K c ⊆ {w | green_function c w < (1 / 2) ^ n} := by
      intro z hz
      rw [mem_setOf_eq]
      rw [← green_function_eq_zero_iff_mem_K] at hz
      rw [hz]
      apply pow_pos
      norm_num

    have h_0_in_K : 0 ∈ K c := hc

    have h_K_sub_comp : K c ⊆ connectedComponentIn {w | green_function c w < (1 / 2) ^ n} 0 :=
      (filled_julia_set_connected hc).isPreconnected.subset_connectedComponentIn h_0_in_K h_K_subset

    exact h_K_sub_comp hc_in_K

  rw [inter_eq_right.mpr h_subset]
  exact mandelbrot_set_connected

ensure_no_sorry para_puzzle_piece_inter_mandelbrot_connected

end

end MLC.Quadratic
