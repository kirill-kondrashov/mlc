import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Escape
import Mlc.Quadratic.Complex.GreenLemmas

/-!
# Green's Function for the Quadratic Family

This file defines the Green's function `G_c(z)` for the filled Julia set `K(c)`.
The Green's function measures the rate of escape to infinity.

## Connection to MLC

The Green's function is used to construct Yoccoz puzzles, which are central to the proof of the
Mandelbrot Local Connectivity (MLC) conjecture.

*   **Equipotentials and Rays**: Level sets of `G_c` (equipotentials) and their orthogonal trajectories
    (external rays) form a grid on `ℂ \ K(c)`.
*   **Yoccoz Puzzles**: Intersections of these curves define puzzle pieces used to analyze the combinatorics
    of orbits.
*   **Böttcher Coordinates**: `G_c` is the real part of the Böttcher coordinate, conjugating `f_c` to `z ↦ z^2`
    near infinity.

## Main Definitions

* `potential_seq c z n`: The sequence `1/2^n * log ‖f_c^n(z)‖`.
* `green_function c z`: The limit of `potential_seq` as `n → ∞`.

## Main Results (Sketched)

* `green_function_eq_zero_iff_mem_K`: `G_c(z) = 0 ↔ z ∈ K(c)`.
* `green_function_functional_eq`: `G_c(f_c(z)) = 2 * G_c(z)`.
* `green_function_harmonic`: `G_c` is harmonic on `ℂ \ K(c)`.

Reference: "Conformal Geometry and Dynamics of Quadratic Polynomials",
https://indico.ictp.it/event/a12182/session/2/contribution/1/material/0/0.pdf
(See Section 21.2 for the definition and properties of the Green's function)
-/

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

variable {c z : ℂ}

set_option maxHeartbeats 400000

/-- The n-th approximation of the Green's function: `1/2^n * log (max 1 ‖f_c^n(z)‖)`. -/
def potential_seq (c z : ℂ) (n : ℕ) : ℝ :=
  (1 / 2 ^ n) * Real.log (max 1 ‖orbit c z n‖)

/-- The Green's function `G_c(z)`. Defined as the limit of `potential_seq`. -/
def green_function (c z : ℂ) : ℝ :=
  limUnder atTop (fun n => potential_seq c z n)

/-- Convergence of the potential sequence to 0 for `z ∈ K(c)`. -/
lemma potential_seq_converges_of_mem_K (h : z ∈ K c) :
    Tendsto (potential_seq c z) atTop (𝓝 0) := by
  rcases h with ⟨M, hM⟩
  let B := Real.log (max 1 M)
  have h_bound : ∀ n, |potential_seq c z n| ≤ (1 / 2 ^ n) * B := by
    intro n
    rw [potential_seq, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    rw [abs_of_nonneg (Real.log_nonneg (le_max_left 1 _))]
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
    apply max_le_max (le_refl 1) (hM n)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => -(1 / 2 ^ n * B))
    (h := fun n => 1 / 2 ^ n * B)
    _
    _
    (fun n => (abs_le.mp (h_bound n)).1)
    (fun n => (abs_le.mp (h_bound n)).2)
  · rw [← neg_zero]
    apply Tendsto.neg
    convert Filter.Tendsto.mul_const B (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1))
    simp [one_div, inv_pow]
    ring
  · convert Filter.Tendsto.mul_const B (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1))
    simp [one_div, inv_pow]
    ring

/-! ### Convergence for escaping points -/

lemma log_orbit_diff_le (c z : ℂ) (n : ℕ) (h : ‖orbit c z n‖ > escape_bound c) :
    |Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖| ≤ 2 * ‖c‖ / ‖orbit c z n‖^2 := by
  let zn := orbit c z n
  let zn1 := orbit c z (n + 1)
  have h_zn : ‖zn‖ > escape_bound c := h
  have h_R : R c ≥ 2 := R_ge_two c
  have h_esc : escape_bound c ≥ R c := escape_bound_ge_R c
  have h_zn_gt_2 : ‖zn‖ > 2 := lt_of_le_of_lt (le_trans h_R h_esc) h_zn
  have h_zn_pos : 0 < ‖zn‖ := lt_trans zero_lt_two h_zn_gt_2
  
  rw [show 2 * Real.log ‖zn‖ = Real.log (‖zn‖ ^ 2) by
    rw [Real.log_pow, Nat.cast_ofNat]
  ]
  
  have h_zn1_eq : zn1 = fc c zn := by
    dsimp [zn1, zn]
    rw [orbit_succ]

  have h_zn_sq_pos : 0 < ‖zn‖^2 := pow_pos h_zn_pos 2
  have h_zn1_pos : 0 < ‖zn1‖ := by
    rw [h_zn1_eq]
    have : ‖fc c zn‖ ≥ ‖zn‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c zn
    apply lt_of_lt_of_le _ this
    have : ‖c‖ < ‖zn‖^2 := by
      have h_esc_nonneg : 0 ≤ escape_bound c := le_trans (le_trans zero_le_two (R_ge_two c)) (escape_bound_ge_R c)
      have h_sq : (escape_bound c)^2 < ‖zn‖^2 := by gcongr
      have h_esc : 2 * ‖c‖ + 1 ≤ (escape_bound c)^2 := escape_bound_sq_ge c
      linarith
    linarith

  rw [← Real.log_div h_zn1_pos.ne' h_zn_sq_pos.ne']
  
  rw [norm_orbit_succ_div_sq_eq c z n h_zn_pos]
  
  let u := c / zn^2
  have h_u_norm : ‖u‖ = ‖c‖ / ‖zn‖^2 := by
    rw [norm_div, norm_pow]
  
  have h_u_le_half : ‖u‖ ≤ 1/2 := norm_u_le_half c z n h
  
  have h_log_bound : |Real.log ‖1 + u‖| ≤ 2 * ‖u‖ := log_bound_helper u h_u_le_half
  
  rw [h_u_norm] at h_log_bound
  rw [le_div_iff₀ (pow_pos h_zn_pos 2)]
  field_simp at h_log_bound
  exact h_log_bound

/-- Convergence of the potential sequence for `z ∉ K(c)`. -/
lemma potential_seq_converges_of_escapes (h : z ∉ K c) :
    ∃ L, Tendsto (potential_seq c z) atTop (𝓝 L) := by
  dsimp [K, boundedOrbit] at h
  push_neg at h
  
  let B := escape_bound c
  obtain ⟨n0, hn0⟩ := h B
  have hn0_R : ‖orbit c z n0‖ > R c := lt_of_le_of_lt (escape_bound_ge_R c) hn0
  
  obtain ⟨N_large, h_growth⟩ := escape_lemma n0 hn0_R B
  
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist ?_)
  
  let a := potential_seq c z
  rw [← summable_nat_add_iff (n0 + N_large)]
  
  have h_bound : ∀ k, dist (a (k + (n0 + N_large))) (a (k + (n0 + N_large) + 1)) ≤ (1 / 2 ^ (k + (n0 + N_large) + 1)) * (2 * ‖c‖ / B^2) := by
    intro k
    let n := k + (n0 + N_large)
    have hn_B : ‖orbit c z n‖ > B := by
      apply h_growth
      dsimp [n]
      linarith
    
    let zn := orbit c z n
    let zn1 := orbit c z (n + 1)
    
    dsimp [a, potential_seq]
    rw [dist_eq_norm, Real.norm_eq_abs]
    
    have h_zn_ge_1 : 1 ≤ ‖zn‖ := le_trans (by norm_num) (le_trans (le_trans (R_ge_two c) (escape_bound_ge_R c)) (le_of_lt hn_B))
    have h_zn1_ge_1 : 1 ≤ ‖zn1‖ := by
      have hzn1_B : ‖zn1‖ > B := by
        apply h_growth
        dsimp [n]
        linarith
      exact le_trans (by norm_num) (le_trans (le_trans (R_ge_two c) (escape_bound_ge_R c)) (le_of_lt hzn1_B))

    rw [max_eq_right h_zn_ge_1]
    rw [max_eq_right h_zn1_ge_1]
    
    have : (1 / 2 ^ n) * Real.log ‖zn‖ = (1 / 2 ^ (n + 1)) * (2 * Real.log ‖zn‖) := by
      rw [pow_succ]
      field_simp
    rw [this]
    
    rw [← mul_sub]
    rw [abs_mul]
    rw [abs_of_nonneg (by positivity)]
    rw [abs_sub_comm]
    
    apply mul_le_mul_of_nonneg_left
    · apply le_trans (log_orbit_diff_le c z n hn_B)
      refine div_le_div_of_nonneg_left ?_ ?_ ?_
      · positivity
      · have h_B_ge_2 : 2 ≤ B := le_trans (R_ge_two c) (escape_bound_ge_R c)
        apply pow_pos (lt_of_lt_of_le (by norm_num) h_B_ge_2) 2
      · apply pow_le_pow_left_of_le
        · have h_B_ge_2 : 2 ≤ B := le_trans (R_ge_two c) (escape_bound_ge_R c)
          linarith
        · apply le_of_lt hn_B
    · positivity

  dsimp [a]
  refine Summable.of_nonneg_of_le (fun k => dist_nonneg) (fun k => h_bound k) ?_
  simp only [pow_add, one_div, mul_inv]
  have : ∀ i : ℕ, (2 ^ i : ℝ)⁻¹ = (2⁻¹) ^ i := fun i => by rw [inv_pow]
  simp_rw [this]
  apply Summable.mul_right
  apply Summable.mul_right
  apply Summable.mul_right
  apply summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- Convergence of the potential sequence for all `z`. -/
lemma potential_seq_converges (c z : ℂ) :
    ∃ L, Tendsto (potential_seq c z) atTop (𝓝 L) := by
  by_cases h : z ∈ K c
  · use 0; exact potential_seq_converges_of_mem_K h
  · exact potential_seq_converges_of_escapes h

/-- `G_c(z)` equals the limit of the potential sequence. -/
lemma green_function_eq_lim (c z : ℂ) :
    Tendsto (potential_seq c z) atTop (𝓝 (green_function c z)) := by
  obtain ⟨L, hL⟩ := potential_seq_converges c z
  have h_eq : green_function c z = L := by
    rw [green_function, limUnder, lim]
    have h_ex : ∃ x, map (potential_seq c z) atTop ≤ 𝓝 x := ⟨L, hL⟩
    have h_spec := Classical.epsilon_spec h_ex
    exact (tendsto_nhds_unique hL h_spec).symm
  rw [h_eq]
  exact hL

/-- The Green's function satisfies the functional equation `G(f(z)) = 2 * G(z)`. -/
lemma green_function_functional_eq (c z : ℂ) :
    green_function c (fc c z) = 2 * green_function c z := by
  have h_lim : Tendsto (fun n => potential_seq c (fc c z) n) atTop (𝓝 (2 * green_function c z)) := by
    have h_shift : ∀ n, potential_seq c (fc c z) n = 2 * potential_seq c z (n + 1) := by
      intro n
      dsimp [potential_seq]
      have h_orb : orbit c (fc c z) n = orbit c z (n + 1) := by
        induction n with
        | zero => simp
        | succ n ih => simp [orbit_succ, ih]
      rw [h_orb]
      rw [pow_succ' 2 n]
      field_simp
    simp_rw [h_shift]
    apply Tendsto.const_mul
    have h_tendsto := green_function_eq_lim c z
    exact h_tendsto.comp (tendsto_add_atTop_nat 1)
  
  have h_eq : green_function c (fc c z) = 2 * green_function c z := by
    rw [green_function, limUnder, lim]
    have h_ex : ∃ x, map (potential_seq c (fc c z)) atTop ≤ 𝓝 x := ⟨2 * green_function c z, h_lim⟩
    have h_spec := Classical.epsilon_spec h_ex
    exact (tendsto_nhds_unique h_lim h_spec).symm
  exact h_eq

/-- The Green's function is non-negative. -/
lemma green_function_nonneg (c z : ℂ) : 0 ≤ green_function c z := by
  sorry

/-- A point is in the filled Julia set iff its Green's function is zero. -/
lemma green_function_eq_zero_iff_mem_K (c z : ℂ) :
    green_function c z = 0 ↔ z ∈ K c := by
  sorry

/-- The Green's function is positive on the basin of infinity. -/
lemma green_function_pos_iff_not_mem_K (c z : ℂ) :
    0 < green_function c z ↔ z ∉ K c := by
  sorry

end

end MLC.Quadratic
