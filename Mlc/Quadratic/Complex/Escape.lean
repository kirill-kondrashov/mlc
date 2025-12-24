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

/-- Escape lemma: if the orbit of z ever leaves the disk of radius R(c), then it
escapes to infinity. -/
lemma escape_lemma (n : ℕ) (h : ‖orbit c z n‖ > R c) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m ≥ N, ‖orbit c z m‖ > M := by
  sorry

end

end MLC.Quadratic
