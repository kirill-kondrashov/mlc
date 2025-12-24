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

lemma R_pos (c : ℂ) : R c > 0 := by
  have := R_ge_two c
  linarith

/-- Escape lemma: if the orbit of z ever leaves the disk of radius R(c), then it
escapes to infinity. -/
lemma escape_lemma (n : ℕ) (h : ‖orbit c z n‖ > R c) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m ≥ N, ‖orbit c z m‖ > M := by
  let w := orbit c z n
  let lam := ‖w‖ - ‖c‖ / ‖w‖
  have hlam : lam > 1 := factor_gt_one c w h
  have hw_pos : ‖w‖ > 0 := lt_trans (R_pos c) h

  have growth : ∀ k, ‖orbit c w k‖ ≥ ‖w‖ * lam ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      let z_k := orbit c w k
      have h_zk_ge : ‖z_k‖ ≥ ‖w‖ := by
        calc ‖z_k‖ ≥ ‖w‖ * lam ^ k := ih
          _ ≥ ‖w‖ * 1 := by
            apply mul_le_mul_of_nonneg_left
            · exact one_le_pow k (le_of_lt hlam)
            · exact le_of_lt hw_pos
          _ = ‖w‖ := by simp

      have h_zk_pos : ‖z_k‖ > 0 := lt_of_lt_of_le hw_pos h_zk_ge

      calc ‖orbit c w (k + 1)‖
        _ = ‖fc c z_k‖ := by rw [orbit_succ]
        _ ≥ ‖z_k‖^2 - ‖c‖ := norm_fc_ge_norm_sq_sub_norm_c c z_k
        _ = ‖z_k‖ * (‖z_k‖ - ‖c‖ / ‖z_k‖) := by field_simp [h_zk_pos.ne']; ring
        _ ≥ ‖z_k‖ * lam := by
          gcongr
          apply (sub_div_mono c).monotoneOn
          · exact hw_pos
          · exact h_zk_pos
          · exact h_zk_ge
        _ ≥ (‖w‖ * lam ^ k) * lam := by
          apply mul_le_mul_of_nonneg_right
          · exact ih
          · exact le_of_lt (lt_trans zero_lt_one hlam)
        _ = ‖w‖ * lam ^ (k + 1) := by rw [pow_succ]; ring

  intro M
  have h_tendsto : Tendsto (fun k => ‖w‖ * lam ^ k) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hw_pos
    apply tendsto_pow_atTop_atTop_of_one_lt hlam

  rcases (Filter.tendsto_atTop_atTop.mp h_tendsto) M with ⟨N0, hN0⟩
  use n + N0
  intro m hm
  let k := m - n
  have hk : m = n + k := by
    rw [Nat.add_comm] at hm
    exact (Nat.sub_eq_of_eq_add (Nat.add_sub_of_le hm).symm).symm
  rw [hk, add_comm]
  dsimp [orbit]
  rw [Function.iterate_add_apply]
  specialize hN0 k (Nat.le_sub_of_add_le hm)
  apply lt_of_lt_of_le hN0
  exact growth k

end

end MLC.Quadratic
