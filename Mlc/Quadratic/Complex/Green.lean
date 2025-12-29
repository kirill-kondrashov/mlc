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
  have h_lim : Tendsto (fun n => - potential_seq c z n) atTop (𝓝 (- green_function c z)) :=
    (green_function_eq_lim c z).neg
  have h_le : - green_function c z ≤ 0 := by
    apply le_of_tendsto' h_lim
    intro n
    simp only [neg_nonpos]
    rw [potential_seq]
    apply mul_nonneg
    · positivity
    · apply Real.log_nonneg
      apply le_max_left
  linarith

lemma green_function_iterate (c z : ℂ) (n : ℕ) :
    green_function c (orbit c z n) = 2^n * green_function c z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ, green_function_functional_eq, ih]
    rw [pow_succ]
    ring

lemma green_function_pos_of_large_norm (c z : ℂ) (h : ‖z‖ > escape_bound c) :
    0 < green_function c z := by
  let B := escape_bound c
  have hB_R : B ≥ R c := escape_bound_ge_R c
  have hR_2 : R c ≥ 2 := R_ge_two c
  have hB_2 : B ≥ 2 := le_trans hR_2 hB_R
  
  have h_orbit_ge : ∀ k, ‖orbit c z k‖ ≥ ‖z‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [orbit_succ]
      have h_zk_ge_z : ‖orbit c z k‖ ≥ ‖z‖ := ih
      have h_zk_gt_R : ‖orbit c z k‖ > R c := lt_of_lt_of_le (lt_of_le_of_lt hB_R h) h_zk_ge_z
      have h_zk_pos : 0 < ‖orbit c z k‖ := lt_trans (lt_of_lt_of_le zero_lt_two hR_2) h_zk_gt_R
      
      calc ‖fc c (orbit c z k)‖ 
        _ ≥ ‖orbit c z k‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c _
        _ = ‖orbit c z k‖ * (‖orbit c z k‖ - ‖c‖ / ‖orbit c z k‖) := by field_simp [h_zk_pos.ne']
        _ ≥ ‖orbit c z k‖ * 1 := by
          gcongr
          have := factor_gt_one c (orbit c z k) h_zk_gt_R
          linarith
        _ = ‖orbit c z k‖ := mul_one _
        _ ≥ ‖z‖ := ih

  have h_diff : ∀ k, |potential_seq c z k - potential_seq c z (k + 1)| ≤ (1 / 2 ^ (k + 1)) * (2 * ‖c‖ / B^2) := by
    intro k
    let zn := orbit c z k
    have h_zn_gt_B : ‖zn‖ > B := lt_of_lt_of_le h (h_orbit_ge k)
    
    have h_log_diff := log_orbit_diff_le c z k h_zn_gt_B
    
    rw [potential_seq, potential_seq]
    rw [max_eq_right (le_trans one_le_two (le_trans hB_2 (le_of_lt h_zn_gt_B)))]
    
    let zn1 := orbit c z (k + 1)
    have h_zn1_gt_B : ‖zn1‖ > B := lt_of_lt_of_le h (h_orbit_ge (k + 1))
    rw [max_eq_right (le_trans one_le_two (le_trans hB_2 (le_of_lt h_zn1_gt_B)))]
    
    rw [pow_succ]
    have : (1 / (2 ^ k * 2)) * Real.log ‖zn1‖ - (1 / 2 ^ k) * Real.log ‖zn‖ = 
           (1 / 2 ^ (k + 1)) * (Real.log ‖zn1‖ - 2 * Real.log ‖zn‖) := by
      field_simp
      ring
    rw [abs_sub_comm]
    rw [this]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    
    apply le_trans (mul_le_mul_of_nonneg_left h_log_diff (by positivity))
    rw [pow_succ]
    gcongr
    rw [div_le_div_iff₀ (pow_pos (lt_trans (lt_of_lt_of_le zero_lt_two hB_2) (le_of_lt h_zn_gt_B)) 2) (pow_pos (lt_of_lt_of_le zero_lt_two hB_2) 2)]
    gcongr
    exact le_of_lt h_zn_gt_B

  have h_cauchy : |potential_seq c z 0 - green_function c z| ≤ 2 * ‖c‖ / B^2 := by
    let C := 2 * ‖c‖ / B^2
    let d := fun k => (1 / 2 ^ (k + 1)) * C
    have h_sum : Summable d := by
      dsimp [d]
      simp_rw [pow_succ, one_div, mul_inv, mul_assoc]
      have : ∀ i : ℕ, (2 ^ i : ℝ)⁻¹ = (2⁻¹) ^ i := fun i => by rw [inv_pow]
      simp_rw [this]
      apply Summable.mul_right
      apply Summable.mul_left
      exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
    
    have h_tsum_eq : ∑' k, d k = C := by
      dsimp [d]
      simp_rw [pow_succ, one_div, mul_inv, mul_assoc]
      have : ∀ i : ℕ, (2 ^ i : ℝ)⁻¹ = (2⁻¹) ^ i := fun i => by rw [inv_pow]
      simp_rw [this]
      rw [tsum_mul_right, tsum_mul_left]
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      field_simp
    
    rw [abs_sub_comm]
    change _ ≤ C
    rw [← h_tsum_eq]
    have h_diff' : ∀ k, dist (potential_seq c z k) (potential_seq c z (k + 1)) ≤ d k := by
      intro k
      rw [dist_eq_norm, Real.norm_eq_abs]
      exact h_diff k
    
    have h_dist_le := dist_le_tsum_of_dist_le_of_tendsto₀ d h_diff' h_sum (green_function_eq_lim c z)
    rw [dist_eq_norm, Real.norm_eq_abs] at h_dist_le
    exact h_dist_le
    
  rw [potential_seq, Nat.cast_zero, pow_zero, inv_one, one_mul] at h_cauchy
  rw [max_eq_right (le_trans one_le_two (le_trans hB_2 (le_of_lt h)))] at h_cauchy
  
  have h_lower : green_function c z ≥ Real.log ‖z‖ - 2 * ‖c‖ / B^2 := by
    linarith [abs_le.mp h_cauchy]
    
  apply lt_of_lt_of_le _ h_lower
  
  have h_log_B : Real.log ‖z‖ > Real.log B := Real.log_lt_log (lt_trans (lt_of_lt_of_le zero_lt_two hB_2) h) h
  apply lt_trans _ h_log_B
  
  by_cases hc : ‖c‖ ≤ 1
  · have hB_eq_2 : B = 2 := by
      rw [escape_bound, R]
      have : 1 + ‖c‖ ≤ 2 := by linarith
      have : Real.sqrt (2 * ‖c‖ + 1) ≤ Real.sqrt 3 := by
        apply Real.sqrt_le_sqrt
        linarith
      have : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt_iff_sq_lt] <;> norm_num
      simp [max_eq_left, this, *]
    rw [hB_eq_2]
    calc 2 * ‖c‖ / 2^2 = ‖c‖ / 2 := by ring
      _ ≤ 1 / 2 := by gcongr
      _ < Real.log 2 := by
        rw [← Real.log_exp (1/2)]
        apply Real.log_lt_log (by positivity)
        apply lt_of_le_of_lt (le_of_lt (Real.add_one_lt_exp _))
        norm_num
  · push_neg at hc
    have hB_eq : B = 1 + ‖c‖ := by
      rw [escape_bound, R]
      have : 1 + ‖c‖ > 2 := by linarith
      have : (1 + ‖c‖)^2 > 2 * ‖c‖ + 1 := by
        nlinarith
      have : 1 + ‖c‖ > Real.sqrt (2 * ‖c‖ + 1) := by
        rw [Real.lt_sqrt_iff_sq_lt]
        · linarith
        · linarith
      simp [max_eq_left, le_of_lt this, le_of_lt (lt_trans zero_lt_two this)]
    rw [hB_eq]
    let u := 1 + ‖c‖
    have hu : u > 2 := by linarith
    have : 2 * ‖c‖ / u^2 < Real.log u := by
      have : 2 * ‖c‖ / u^2 < 1/2 := by
        rw [div_lt_iff₀ (pow_pos (lt_trans zero_lt_two hu) 2)]
        rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        dsimp [u]
        nlinarith
      apply lt_trans this
      rw [← Real.log_exp (1/2)]
      apply Real.log_lt_log (by positivity)
      apply lt_trans (Real.add_one_lt_exp (1/2))
      apply lt_trans (by norm_num : 1 + 1/2 = 1.5 < 2) hu
    exact this

/-- A point is in the filled Julia set iff its Green's function is zero. -/
lemma green_function_eq_zero_iff_mem_K (c z : ℂ) :
    green_function c z = 0 ↔ z ∈ K c := by
  constructor
  · intro h
    by_contra h_esc
    dsimp [K, boundedOrbit] at h_esc
    push_neg at h_esc
    obtain ⟨n, hn⟩ := h_esc (escape_bound c)
    have h_pos : 0 < green_function c (orbit c z n) := 
      green_function_pos_of_large_norm c (orbit c z n) hn
    rw [green_function_iterate] at h_pos
    rw [h, mul_zero] at h_pos
    linarith
  · intro h
    apply le_antisymm
    · have h_lim := potential_seq_converges_of_mem_K h
      rw [green_function]
      exact le_of_eq (tendsto_nhds_unique (green_function_eq_lim c z) h_lim)
    · exact green_function_nonneg c z

/-- The Green's function is positive on the basin of infinity. -/
lemma green_function_pos_iff_not_mem_K (c z : ℂ) :
    0 < green_function c z ↔ z ∉ K c := by
  rw [← not_iff_not]
  push_neg
  have : green_function c z ≤ 0 ↔ green_function c z = 0 := by
    constructor
    · intro h; exact le_antisymm h (green_function_nonneg c z)
    · intro h; rw [h]
  rw [this]
  rw [green_function_eq_zero_iff_mem_K]

end

end MLC.Quadratic
