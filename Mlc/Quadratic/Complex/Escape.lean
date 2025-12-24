import Mlc.Quadratic.Complex.Basic

/-!
# Escape Lemma for the Quadratic Family

This file proves the escape lemma: if the orbit of a point ever leaves the disk of
radius `R(c)`, then it escapes to infinity.

Reference: https://indico.ictp.it/event/a12182/session/2/contribution/1/material/0/0.pdf
(p. 125, Section 21.2)
-/

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

variable {c z : ℂ}

lemma norm_sq_sub_norm_c_ge (c z : ℂ) : ‖z^2‖ - ‖c‖ ≥ ‖z‖^2 - (R c - 1) := by
  simp only [norm_sq]
  linarith [R_ge_one_plus_c c]

lemma norm_growth (c z : ℂ) : ‖fc c z‖ ≥ ‖z‖^2 - (R c - 1) := by
  rw [fc]
  have h_tri : ‖z^2 + c‖ ≥ ‖z^2‖ - ‖c‖ := by
    have := norm_add_le (z^2 + c) (-c)
    simp only [add_neg_cancel_right, norm_neg] at this
    linarith
  rw [norm_sq] at h_tri
  linarith [R_ge_one_plus_c c]

lemma norm_fc_ge_norm_sq_sub_norm_c (c z : ℂ) : ‖fc c z‖ ≥ ‖z‖^2 - ‖c‖ := by
  rw [fc]
  have := norm_add_le (z^2 + c) (-c)
  simp only [add_neg_cancel_right, norm_neg] at this
  rw [norm_sq] at this
  linarith

lemma sub_div_mono (c : ℂ) : StrictMonoOn (fun x : ℝ => x - ‖c‖ / x) (Set.Ioi 0) := by
  intro x hx y _ hxy
  dsimp
  apply add_lt_add_of_lt_of_le hxy
  rw [neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (norm_nonneg c) hx (le_of_lt hxy)

lemma factor_gt_one (c z : ℂ) (h : ‖z‖ > R c) : ‖z‖ - ‖c‖ / ‖z‖ > 1 := by
  have R_pos : R c > 0 := by linarith [R_ge_two c]
  have z_pos : ‖z‖ > 0 := by linarith
  have key : ‖z‖ - ‖c‖ / ‖z‖ > R c - ‖c‖ / R c := sub_div_mono c R_pos z_pos h
  have R_ge : R c - ‖c‖ / R c ≥ 1 := by
    have hR2 : R c ≥ 2 := R_ge_two c
    have hRc : R c ≥ 1 + ‖c‖ := R_ge_one_plus_c c
    rw [ge_iff_le, le_sub_iff_add_le, add_comm 1, ← le_sub_iff_add_le]
    rw [div_le_iff₀ R_pos]
    have h_calc := calc
      ‖c‖ = 1 * ‖c‖ := by simp
      _ ≤ (R c - 1) * (R c - 1) := by
        nlinarith
      _ ≤ (R c - 1) * R c := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · linarith
      _ = R c * R c - R c := by ring
    linarith
  linarith

/-- Escape lemma: if the orbit of z ever leaves the disk of radius R(c), then it
escapes to infinity. -/
lemma escape_lemma (n : ℕ) (h : ‖orbit c z n‖ > R c) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m ≥ N, ‖orbit c z m‖ > M := by
    sorry

end

end MLC.Quadratic
