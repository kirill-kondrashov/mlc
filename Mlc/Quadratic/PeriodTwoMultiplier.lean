import Mlc.Quadratic.Complex.FirstComponents

/-!
# The multiplier map of the period-two component

The attracting cycle of prime period two of `z² + c` has multiplier `4(c + 1)`, and the
period-two component is the disk `|c + 1| < 1/4`.  The multiplier map is therefore the affine
biholomorphism `c ↦ 4(c + 1)` from this disk onto the unit disk, with inverse `m ↦ m/4 - 1`.
This is the period-two analogue of the period-one statement in `MultiplierMap`.
-/

namespace MLC.Quadratic.PeriodTwoMultiplier

open Complex Metric Set

noncomputable section

/-- The period-two component. -/
def period2Component : Set ℂ := {c : ℂ | MLC.Quadratic.FirstComponents.HasAttractingPeriodTwoCycle c}

/-- The multiplier of the period-two component. -/
def period2Multiplier (c : ℂ) : ℂ := 4 * (c + 1)

theorem period2Component_eq : period2Component = ball (-1 : ℂ) (1 / 4) := by
  ext c
  exact MLC.Quadratic.FirstComponents.hasAttractingPeriodTwoCycle_iff c

theorem period2Multiplier_biholomorphic :
    (∀ c ∈ period2Component, period2Multiplier c ∈ ball (0 : ℂ) 1) ∧
    (∀ m ∈ ball (0 : ℂ) 1, m / 4 - 1 ∈ period2Component) ∧
    (∀ c ∈ period2Component, period2Multiplier c / 4 - 1 = c) ∧
    (∀ m ∈ ball (0 : ℂ) 1, period2Multiplier (m / 4 - 1) = m) ∧
    Differentiable ℂ period2Multiplier ∧
    Differentiable ℂ (fun m : ℂ => m / 4 - 1) := by
  rw [period2Component_eq]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [mem_ball, dist_eq_norm, sub_neg_eq_add] at hc
    rw [mem_ball_zero_iff]
    unfold period2Multiplier
    rw [norm_mul, h4]
    linarith
  · intro m hm
    rw [mem_ball_zero_iff] at hm
    rw [mem_ball, dist_eq_norm, sub_neg_eq_add]
    have hshift : m / 4 - 1 + 1 = m / 4 := by ring
    rw [hshift, norm_div, h4]
    linarith
  · intro c _
    unfold period2Multiplier
    ring
  · intro m _
    unfold period2Multiplier
    ring
  · unfold period2Multiplier
    fun_prop
  · fun_prop

end

end MLC.Quadratic.PeriodTwoMultiplier
