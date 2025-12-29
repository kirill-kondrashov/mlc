import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green

/-!
# Böttcher Coordinates

This file defines the Böttcher coordinate `φ_c(z)` which conjugates `f_c(z)` to `z^2`
in a neighborhood of infinity.

## Main Definitions

* `bottcher_coord c z`: The Böttcher coordinate map.

## Main Results (Sketched)

* `bottcher_conjugates`: `φ_c(f_c(z)) = (φ_c(z))^2`.
* `bottcher_asymptotic`: `φ_c(z) ~ z` as `z → ∞`.
* `log_norm_bottcher_eq_green`: `log ‖φ_c(z)‖ = G_c(z)`.

-/

namespace MLC.Quadratic

open scoped Complex
open Complex Topology Filter Real

noncomputable section

variable {c z : ℂ}

/-- The Böttcher coordinate `φ_c(z)`.
Ideally defined as `lim_{n→∞} (f_c^n(z))^(1/2^n)`.
For now, we declare it as a constant to sketch the interface. -/
def bottcher_coord (c z : ℂ) : ℂ :=
  sorry

/-- The Böttcher coordinate conjugates `f_c` to `z^2`. -/
lemma bottcher_conjugates (c z : ℂ) (h : R c < ‖z‖) :
    bottcher_coord c (fc c z) = (bottcher_coord c z) ^ 2 := by
  sorry

/-- The norm of the Böttcher coordinate is related to the Green's function. -/
lemma log_norm_bottcher_eq_green (c z : ℂ) (h : R c < ‖z‖) :
    Real.log ‖bottcher_coord c z‖ = green_function c z := by
  sorry

end

end MLC.Quadratic
