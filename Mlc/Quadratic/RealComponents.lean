import Mlc.Quadratic.Complex.FirstComponents

/-!
# Real parameters in the first hyperbolic components

For real parameters the two components of the previous module meet the real line in
open intervals: the main cardioid `H₀` in `(-3/4, 1/4)`, and the period-two disk `H₂` in
`(-5/4, -3/4)`.  The main cardioid is parametrized by `t ↦ t/2 - t²/4` on the unit disk; a
real parameter in it comes from a real multiplier.
-/

namespace MLC.Quadratic.RealComponents

open Complex Metric Set

noncomputable section

theorem hasAttractingFixedPoint_ofReal_iff (x : ℝ) :
    MLC.Quadratic.FirstComponents.HasAttractingFixedPoint (x : ℂ) ↔
      -(3 / 4) < x ∧ x < 1 / 4 := by
  rw [MLC.Quadratic.FirstComponents.hasAttractingFixedPoint_iff_mem_image]
  constructor
  · rintro ⟨t, ht, hx⟩
    have hn : ‖t‖ < 1 := mem_ball_zero_iff.mp ht
    have hsq : ‖t‖ ^ 2 < 1 := by nlinarith [norm_nonneg t]
    rw [Complex.sq_norm, Complex.normSq_apply] at hsq
    have hre := congrArg Complex.re hx
    have him := congrArg Complex.im hx
    simp [MLC.Quadratic.FirstComponents.cardioidMap, pow_two] at hre him
    have hb : t.im * (1 - t.re) = 0 := by linear_combination 2 * him
    have hre1 : t.re < 1 := by nlinarith [sq_nonneg t.im]
    have hb0 : t.im = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exfalso
        linarith
    rw [hb0] at hre hsq
    have ha : t.re ^ 2 < 1 := by nlinarith
    have ha1 : -1 < t.re := by nlinarith
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (t.re - 1)]
  · rintro ⟨h1, h2⟩
    have hspos : 0 < Real.sqrt (1 - 4 * x) := Real.sqrt_pos.mpr (by linarith)
    have hs0 : 0 ≤ Real.sqrt (1 - 4 * x) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (1 - 4 * x) ^ 2 = 1 - 4 * x := Real.sq_sqrt (by linarith)
    have hs_lt : Real.sqrt (1 - 4 * x) < 2 := by nlinarith
    set s := Real.sqrt (1 - 4 * x) with hs
    refine ⟨((1 - s : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    · unfold MLC.Quadratic.FirstComponents.cardioidMap
      have key : (1 - s) / 2 - (1 - s) ^ 2 / 4 = x := by
        linear_combination (-1 / 4 : ℝ) * hs2
      have hcast : ((1 - s : ℝ) : ℂ) / 2 - ((1 - s : ℝ) : ℂ) ^ 2 / 4
          = (((1 - s) / 2 - (1 - s) ^ 2 / 4 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, key]

theorem hasAttractingPeriodTwoCycle_ofReal_iff (x : ℝ) :
    MLC.Quadratic.FirstComponents.HasAttractingPeriodTwoCycle (x : ℂ) ↔
      -(5 / 4) < x ∧ x < -(3 / 4) := by
  have hshift : (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [MLC.Quadratic.FirstComponents.hasAttractingPeriodTwoCycle_iff, mem_ball, dist_eq_norm,
    sub_neg_eq_add, hshift, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

end

end MLC.Quadratic.RealComponents
