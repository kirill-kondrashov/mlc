import Mlc.Quadratic.Complex.BottcherOnMTheory
import Mathlib.Analysis.Analytic.Order

namespace MLC

open Quadratic Complex Topology Set Filter

theorem analyticOrderAt_sub_ge_two_of_deriv_eq_zero
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hderiv : deriv f z = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (fun w => f w - f z) z := by
  have hderiv_analytic : AnalyticAt ℂ (deriv f) z := hf.deriv
  have hderiv_order_ne_zero : analyticOrderAt (deriv f) z ≠ 0 := by
    -- analyticOrderAt ≠ 0 iff the function vanishes at the point
    exact (AnalyticAt.analyticOrderAt_ne_zero (f := deriv f) hderiv_analytic).2 hderiv
  have hderiv_order_ge_one : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) z := by
    cases h : analyticOrderAt (deriv f) z with
    | top =>
        simp
    | coe n =>
        have hn0 : n ≠ 0 := by
          intro hn0
          apply hderiv_order_ne_zero
          simp [h, hn0]
        have hn1 : (1 : ℕ) ≤ n := by
          exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
        have h' : (1 : ℕ∞) ≤ (n : ℕ∞) := by
          exact_mod_cast hn1
        simpa [h] using h'
  have horder :
      analyticOrderAt (deriv f) z + 1 = analyticOrderAt (fun w => f w - f z) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (AnalyticAt.analyticOrderAt_deriv_add_one (f := f) (x := z) hf)
  have h2 : (2 : ℕ∞) ≤ analyticOrderAt (deriv f) z + 1 := by
    -- 2 ≤ x + 1 if 1 ≤ x.
    simpa [one_add_one_eq_two, add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hderiv_order_ge_one (1 : ℕ∞))
  exact h2.trans (by simp [horder])

end MLC
