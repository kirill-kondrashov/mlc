import Mlc.Quadratic.Complex.FirstComponents
import Mlc.Quadratic.RealComponents

/-!
# The multiplier map of the main cardioid is a biholomorphism

For `c` in the main cardioid `H₀`, the attracting fixed point of `z² + c` has multiplier
`t` in the unit disk with `t/2 - t²/4 = c`.  The multiplier is given explicitly by the
principal square root:

  `t = 1 - √(1 - 4c)`,

and this formula is holomorphic on `H₀`.  Hence the multiplier map `H₀ → 𝔻` is a conformal
isomorphism with inverse `t ↦ t/2 - t²/4`.  This is the period-one case of the multiplier
theorem in Lyubich's notes.
-/

namespace MLC.Quadratic.MultiplierMap

open Complex Metric Set

noncomputable section

/-- The principal square root of `1 - 4c`, through the principal logarithm. -/
def mainSqrt (c : ℂ) : ℂ := Complex.exp (Complex.log (1 - 4 * c) / 2)

/-- The multiplier of the attracting fixed point of the main cardioid. -/
def mainMultiplier (c : ℂ) : ℂ := 1 - mainSqrt c

/-- The main cardioid. -/
def mainCardioid : Set ℂ := {c : ℂ | MLC.Quadratic.FirstComponents.HasAttractingFixedPoint c}

lemma mainSqrt_sq {c : ℂ} (h : 1 - 4 * c ≠ 0) : mainSqrt c ^ 2 = 1 - 4 * c := by
  unfold mainSqrt
  rw [← Complex.exp_nat_mul]
  have hw : ((2 : ℕ) : ℂ) * (Complex.log (1 - 4 * c) / 2) = Complex.log (1 - 4 * c) := by
    push_cast
    ring
  rw [hw, Complex.exp_log h]

lemma re_mainSqrt_nonneg (c : ℂ) : 0 ≤ (mainSqrt c).re := by
  unfold mainSqrt
  rw [Complex.exp_re]
  apply mul_nonneg (Real.exp_pos _).le
  have harg : (Complex.log (1 - 4 * c) / 2).im = Complex.arg (1 - 4 * c) / 2 := by
    simp [Complex.log_im]
  rw [harg]
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have := Complex.neg_pi_lt_arg (1 - 4 * c)
    linarith [Real.pi_pos]
  · have := Complex.arg_le_pi (1 - 4 * c)
    linarith [Real.pi_pos]

lemma cardioidMap_mainMultiplier {c : ℂ} (h : 1 - 4 * c ≠ 0) :
    MLC.Quadratic.FirstComponents.cardioidMap (mainMultiplier c) = c := by
  have hsq := mainSqrt_sq h
  unfold MLC.Quadratic.FirstComponents.cardioidMap mainMultiplier
  linear_combination (-1 / 4 : ℂ) * hsq

/-- If `t` lies in the unit disk and `t/2 - t²/4 = c`, then `t` is the principal multiplier. -/
lemma eq_mainMultiplier_of_cardioidMap {c t : ℂ} (hc : MLC.Quadratic.FirstComponents.cardioidMap t = c)
    (ht : ‖t‖ < 1) (h : 1 - 4 * c ≠ 0) : t = mainMultiplier c := by
  have hsq := mainSqrt_sq h
  have hkey : (1 - t - mainSqrt c) * (1 - t + mainSqrt c) = 0 := by
    unfold MLC.Quadratic.FirstComponents.cardioidMap at hc
    linear_combination (-4 : ℂ) * hc + (-1 : ℂ) * hsq
  rcases mul_eq_zero.mp hkey with h1 | h1
  · unfold mainMultiplier
    linear_combination (-1 : ℂ) * h1
  · exfalso
    have hteq : t = 1 + mainSqrt c := by linear_combination (-1 : ℂ) * h1
    have hre1 : 1 ≤ t.re := by
      rw [hteq, Complex.add_re, Complex.one_re]
      linarith [re_mainSqrt_nonneg c]
    have hle := Complex.re_le_norm t
    linarith

/-- A parameter in the main cardioid is not `1/4`. -/
lemma one_sub_four_mul_ne_zero {c : ℂ} (hc : MLC.Quadratic.FirstComponents.HasAttractingFixedPoint c) :
    1 - 4 * c ≠ 0 := by
  rw [MLC.Quadratic.FirstComponents.hasAttractingFixedPoint_iff_mem_image] at hc
  obtain ⟨t, ht, rfl⟩ := hc
  intro h0
  have hsq : (1 - t) ^ 2 = 0 := by
    unfold MLC.Quadratic.FirstComponents.cardioidMap at h0
    linear_combination h0
  have ht1 : t = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linear_combination (-1 : ℂ) * this
  have hn : ‖t‖ < 1 := mem_ball_zero_iff.mp ht
  rw [ht1, norm_one] at hn
  exact lt_irrefl _ hn

/-- The main cardioid is contained in the slit plane of `1 - 4c`. -/
lemma one_sub_four_mul_mem_slitPlane {c : ℂ}
    (hc : MLC.Quadratic.FirstComponents.HasAttractingFixedPoint c) :
    1 - 4 * c ∈ slitPlane := by
  by_cases him : c.im = 0
  · have hcr : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hcr] at hc
    have hbounds := (MLC.Quadratic.RealComponents.hasAttractingFixedPoint_ofReal_iff c.re).mp hc
    rw [Complex.mem_slitPlane_iff]
    left
    simp
    linarith [hbounds.1, hbounds.2]
  · rw [Complex.mem_slitPlane_iff]
    right
    simp
    exact fun h => him (by linarith)

lemma differentiableAt_mainMultiplier {c : ℂ} (hc : 1 - 4 * c ∈ slitPlane) :
    DifferentiableAt ℂ mainMultiplier c := by
  have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 - 4 * w) c := by fun_prop
  have h2 := ((h1.clog hc).div_const 2).cexp
  exact (h2.const_sub 1)

theorem multiplier_map_biholomorphic :
    (∀ c ∈ mainCardioid, mainMultiplier c ∈ ball (0 : ℂ) 1) ∧
    (∀ t ∈ ball (0 : ℂ) 1, MLC.Quadratic.FirstComponents.cardioidMap t ∈ mainCardioid) ∧
    (∀ c ∈ mainCardioid, MLC.Quadratic.FirstComponents.cardioidMap (mainMultiplier c) = c) ∧
    (∀ t ∈ ball (0 : ℂ) 1, mainMultiplier (MLC.Quadratic.FirstComponents.cardioidMap t) = t) ∧
    DifferentiableOn ℂ mainMultiplier mainCardioid ∧
    DifferentiableOn ℂ MLC.Quadratic.FirstComponents.cardioidMap (ball (0 : ℂ) 1) := by
  have hsmall : ∀ c ∈ mainCardioid, mainMultiplier c ∈ ball (0 : ℂ) 1 := by
    intro c hc
    obtain ⟨z, hz, hn⟩ := hc
    have hne : 1 - 4 * c ≠ 0 := one_sub_four_mul_ne_zero ⟨z, hz, hn⟩
    have hcz : MLC.Quadratic.FirstComponents.cardioidMap (2 * z) = c := by
      have hfix : z ^ 2 + c = z := hz
      unfold MLC.Quadratic.FirstComponents.cardioidMap
      linear_combination (-1 : ℂ) * hfix
    rw [MLC.Quadratic.FirstComponents.deriv_fc] at hn
    have ht : ‖2 * z‖ < 1 := hn
    have hmul := eq_mainMultiplier_of_cardioidMap hcz ht hne
    rw [mem_ball_zero_iff, ← hmul]
    exact ht
  refine ⟨hsmall, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (MLC.Quadratic.FirstComponents.hasAttractingFixedPoint_iff_mem_image _).mpr ⟨t, ht, rfl⟩
  · intro c hc
    exact cardioidMap_mainMultiplier (one_sub_four_mul_ne_zero hc)
  · intro t ht
    have hc : MLC.Quadratic.FirstComponents.cardioidMap t ∈ mainCardioid :=
      (MLC.Quadratic.FirstComponents.hasAttractingFixedPoint_iff_mem_image _).mpr ⟨t, ht, rfl⟩
    have hmem := hsmall _ hc
    have hinj := MLC.Quadratic.FirstComponents.cardioidMap_injOn_closedBall
      (ball_subset_closedBall hmem) (ball_subset_closedBall ht)
      (cardioidMap_mainMultiplier (one_sub_four_mul_ne_zero hc))
    exact hinj
  · intro c hc
    exact (differentiableAt_mainMultiplier (one_sub_four_mul_mem_slitPlane hc)).differentiableWithinAt
  · exact MLC.Quadratic.FirstComponents.cardioidMap_differentiable.differentiableOn

end

end MLC.Quadratic.MultiplierMap
