import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Escape

/-!
# Green's Function for the Quadratic Family

This file defines the Green's function `G_c(z)` for the filled Julia set `K(c)`.
The Green's function measures the rate of escape to infinity.

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

/-- The n-th approximation of the Green's function: `1/2^n * log ‖f_c^n(z)‖`. -/
def potential_seq (c z : ℂ) (n : ℕ) : ℝ :=
  (1 / 2 ^ n) * Real.log ‖orbit c z n‖

/-- The Green's function `G_c(z)`. Defined as the limit of `potential_seq`. -/
def green_function (c z : ℂ) : ℝ :=
  limUnder atTop (fun n => potential_seq c z n)

/-- The Green's function satisfies the functional equation `G(f(z)) = 2 * G(z)`. -/
lemma green_function_functional_eq (c z : ℂ) :
    green_function c (fc c z) = 2 * green_function c z := by
  sorry

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
