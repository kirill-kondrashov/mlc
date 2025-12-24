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
    rw [ge_iff_le, div_le_iff R_pos, sub_mul, div_mul_cancel₀ _ (ne_of_gt R_pos)]
    rw [le_sub_iff_add_le]
    by_cases hc : 1 + ‖c‖ ≤ 2
    · have : ‖c‖ ≤ 1 := by linarith
      calc
        R c + ‖c‖ = 2 + ‖c‖ := by simp [R, hc]
        _ ≤ 2 + 1 := by gcongr
        _ ≤ 2 * 2 := by norm_num
        _ ≤ R c * R c := by gcongr
    · have : R c = 1 + ‖c‖ := by simp [R, hc]; linarith
      rw [this]
      nlinarith
  linarith

/-- Escape lemma: if the orbit of z ever leaves the disk of radius R(c), then it
escapes to infinity. -/
lemma escape_lemma (n : ℕ) (h : ‖orbit c z n‖ > R c) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m ≥ N, ‖orbit c z m‖ > M := by
  let z_n := orbit c z n
  let K := ‖z_n‖ - ‖c‖ / ‖z_n‖
  have hK : K > 1 := factor_gt_one c z_n h
  have h_growth : ∀ k, ‖orbit c z (n + k)‖ ≥ K ^ k * ‖z_n‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      let z_nk := orbit c z (n + k)
      have h_znk_gt : ‖z_nk‖ > R c := by
        calc
          ‖z_nk‖ ≥ K ^ k * ‖z_n‖ := ih
          _ > 1 ^ k * R c := by gcongr
          _ = R c := by simp
      have h_step : ‖fc c z_nk‖ ≥ ‖z_nk‖ * K := by
        have : ‖fc c z_nk‖ ≥ ‖z_nk‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c z_nk
        rw [sq, ← mul_sub] at this
        apply ge_trans this
        gcongr
        have z_n_pos : 0 < ‖z_n‖ := by linarith [R_ge_two c, h]
        have z_nk_pos : 0 < ‖z_nk‖ := by linarith [R_ge_two c, h_znk_gt]
        apply (sub_div_mono c).monotoneOn z_n_pos z_nk_pos
        calc
          ‖z_n‖ = 1 * ‖z_n‖ := by simp
          _ ≤ K ^ k * ‖z_n‖ := by
            gcongr
            exact one_le_pow_of_one_le (le_of_lt hK) k
          _ ≤ ‖z_nk‖ := ih
      rw [orbit_succ, add_assoc, add_comm 1 k, ← add_assoc]
      calc
        ‖fc c z_nk‖ ≥ ‖z_nk‖ * K := h_step
        _ ≥ (K ^ k * ‖z_n‖) * K := by gcongr
        _ = K ^ (k + 1) * ‖z_n‖ := by ring

  intro M
  have h_unbounded : Tendsto (fun k => K ^ k * ‖z_n‖) atTop atTop := by
    apply Tendsto.atTop_mul_const_of_pos
    · exact tendsto_pow_atTop_of_one_lt hK
    · linarith [h, R_ge_two c]

  obtain ⟨k0, hk0⟩ := (atTop_basis.tendsto_iff atTop_basis).mp h_unbounded M
  use n + k0
  intro m hm
  let k := m - n
  have hk : k ≥ k0 := Nat.le_sub_of_add_le hm
  rw [← Nat.sub_add_cancel (le_trans (le_add_right n k0) hm)]
  apply lt_of_lt_of_le (hk0 k hk)
  exact h_growth k

end

end MLC.Quadratic
