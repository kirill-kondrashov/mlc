import Mlc.Quadratic.Complex.Basic

/-!
# Escape Lemma for the Quadratic Family
This file proves the escape lemma: if the orbit of a point ever leaves the disk of radius `R(c)`, then it escapes to infinity.
-/
namespace MLC
namespace Quadratic
open scoped Complex
open Complex Topology Filter Real
noncomputable section

variable {c z : ℂ}

/-- Helper lemmas. -/
lemma norm_sq_sub_norm_c_ge (c : ℂ) :
    ∀ z : ℂ, ‖z^2‖ - ‖c‖ ≥ ‖z‖^2 - (R c - 1) := by
  intro z
  rw [norm_sq]
  linarith [R_ge_one_plus_c c]

lemma norm_growth (c z : ℂ) (h : ‖z‖ > R c) :
    ‖fc c z‖ ≥ ‖z‖^2 - (R c - 1) := by
  rw [fc]
  rw [← norm_sq]
  have: ‖z^2 + c‖ ≥ ‖z^2‖ - ‖c‖ := by
    sorry
  rw [norm_sq] at this
  sorry


/--
Escape lemma: if the orbit of z ever leaves the disk of radius R(c), then it
escapes to infinity.

https://indico.ictp.it/event/a12182/session/2/contribution/1/material/0/0.pdf

p. 125

21.2. Looking from infinity. The first observation is that ...
-/
lemma escape_lemma (n : ℕ) (h : ‖orbit c z n‖ > R c) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ m ≥ N, ‖orbit c z m‖ > M := by sorry

end
end Quadratic
end MLC
