import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Escape

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

lemma log_ge_one_sub_inv {x : ℝ} (hx : 0 < x) : Real.log x ≥ 1 - 1/x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  rw [inv_eq_one_div] at h
  linarith

lemma abs_log_le_two_mul_abs_sub_one {x : ℝ} (hx : 0.5 ≤ x) : |Real.log x| ≤ 2 * |x - 1| := by
  by_cases h1 : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (sub_nonneg.mpr h1)]
    apply le_trans (Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) h1))
    linarith
  · push_neg at h1
    rw [abs_of_neg (Real.log_neg (by linarith) h1), abs_of_neg (sub_neg.mpr h1)]
    have h_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
    have h_log : Real.log x ≥ 1 - 1/x := log_ge_one_sub_inv h_pos
    rw [neg_sub]
    have h_ineq : 1 - 1/x ≥ 2 * x - 2 := by
      rw [ge_iff_le]
      rw [← mul_le_mul_iff_left₀ h_pos]
      rw [sub_mul]
      field_simp [h_pos.ne']
      have h_sub_neg : x - 1 < 0 := by linarith
      nth_rw 2 [← one_mul (x - 1)]
      rw [mul_le_mul_right_of_neg h_sub_neg]
      linarith
    linarith

variable {c z : ℂ}

/-- A bound used to ensure the orbit is large enough for the log approximation. -/
def escape_bound (c : ℂ) : ℝ := max (R c) (Real.sqrt (2 * ‖c‖ + 1))

lemma escape_bound_ge_R (c : ℂ) : R c ≤ escape_bound c := le_max_left _ _

lemma escape_bound_sq_ge (c : ℂ) : 2 * ‖c‖ + 1 ≤ (escape_bound c)^2 := by
  have h_nonneg : 0 ≤ 2 * ‖c‖ + 1 := by positivity
  have h_sqrt : Real.sqrt (2 * ‖c‖ + 1) ≤ escape_bound c := le_max_right _ _
  rw [Real.sqrt_le_iff] at h_sqrt
  exact h_sqrt.2

lemma norm_orbit_succ_div_sq_eq (c z : ℂ) (n : ℕ) (h_zn_pos : 0 < ‖orbit c z n‖) :
    ‖orbit c z (n + 1)‖ / ‖orbit c z n‖^2 = ‖1 + c / (orbit c z n)^2‖ := by
  let zn := orbit c z n
  let zn1 := orbit c z (n + 1)
  have h_zn1_eq : zn1 = zn^2 + c := by
    dsimp [zn1, zn]
    rw [orbit_succ, fc]
  change ‖zn1‖ / ‖zn‖^2 = _
  rw [h_zn1_eq]
  have h_zn_sq_ne_zero : zn^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mp (ne_of_gt h_zn_pos))
  rw [div_eq_iff (ne_of_gt (pow_pos h_zn_pos 2))]
  rw [← norm_pow]
  rw [← norm_mul]
  congr
  rw [add_mul, one_mul, div_mul_cancel₀ _ h_zn_sq_ne_zero, add_comm]

lemma norm_u_le_half (c z : ℂ) (n : ℕ) (h : ‖orbit c z n‖ > escape_bound c) :
    ‖c / (orbit c z n)^2‖ ≤ 1/2 := by
  let zn := orbit c z n
  have h_zn : ‖zn‖ > escape_bound c := h
  have h_R : R c ≥ 2 := R_ge_two c
  have h_esc : escape_bound c ≥ R c := escape_bound_ge_R c
  have h_zn_gt_2 : ‖zn‖ > 2 := lt_of_le_of_lt (le_trans h_R h_esc) h_zn
  have h_zn_pos : 0 < ‖zn‖ := lt_trans zero_lt_two h_zn_gt_2
  
  rw [norm_div, norm_pow]
  rw [div_le_iff₀ (pow_pos h_zn_pos 2)]
  rw [← mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 2)]
  field_simp
  have h_le : 2 * ‖c‖ ≤ 2 * ‖c‖ + 1 := le_add_of_nonneg_right zero_le_one
  apply le_trans h_le
  apply le_trans (escape_bound_sq_ge c)
  apply le_of_lt
  gcongr
  apply le_trans (Real.sqrt_nonneg _) (le_max_right _ _)

lemma log_bound_helper (u : ℂ) (hu : ‖u‖ ≤ 1/2) :
    |Real.log ‖1 + u‖| ≤ 2 * ‖u‖ := by
  apply le_trans (abs_log_le_two_mul_abs_sub_one _)
  · rw [mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 2)]
    rw [abs_le]
    constructor
    · rw [neg_le_sub_iff_le_add]
      have := norm_sub_norm_le 1 (-u)
      simp at this
      linarith
    · rw [sub_le_iff_le_add]
      have := norm_add_le 1 u
      simp at this
      linarith
  · have := norm_sub_norm_le 1 (-u)
    simp at this
    linarith

lemma pow_le_pow_left_of_le {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hxy : x ≤ y) : x^n ≤ y^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    rw [mul_comm (x^n), mul_comm (y^n)]
    apply mul_le_mul hxy ih (pow_nonneg hx n) (le_trans hx hxy)

end

end MLC.Quadratic
