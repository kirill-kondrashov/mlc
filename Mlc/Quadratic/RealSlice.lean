import Yoccoz.Quadratic.Complex.Basic

/-!
# The real slice of the Mandelbrot set

For real `x`, the Mandelbrot set meets the real line exactly in `[-2, 1/4]`.
The proof follows the classical argument in Milnor's *Dynamics in One Complex
Variable* and in Douady and Hubbard's exposition:

* if `‖c‖ > 2` the orbit of `0` escapes, with a linear lower bound on the norms;
* for real `x > 1/4` the real orbit of `0` increases by at least `x - 1/4`;
* for `x ∈ [-2, 1/4]` the orbit of `0` stays in the interval `[-β, β]`, where
  `β = (1 + √(1 - 4x))/2` is the positive fixed point of `t ↦ t² + x`.
-/

namespace MLC.Quadratic.RealSlice

open Complex

/-- The real orbit of `0` under `t ↦ t² + c`. -/
def realOrbit (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => realOrbit c n ^ 2 + c

lemma orbit_ofReal (c : ℝ) (n : ℕ) :
    orbit (c : ℂ) 0 n = (realOrbit c n : ℂ) := by
  induction n with
  | zero => simp [realOrbit]
  | succ n ih => simp [orbit_succ, fc, realOrbit, ih]

/-- If `‖c‖ = a > 2`, then the norms of the orbit of `0` grow at least linearly with
increment `a(a - 2)`. -/
lemma norm_orbit_ge_of_two_lt_norm (c : ℂ) (hc : 2 < ‖c‖) (n : ℕ) :
    ‖c‖ + n * (‖c‖ * (‖c‖ - 2)) ≤ ‖orbit c 0 (n + 1)‖ := by
  induction n with
  | zero => simp [orbit_succ, fc]
  | succ n ih =>
    have hδ0 : 0 ≤ ‖c‖ * (‖c‖ - 2) := mul_nonneg (by linarith) (by linarith)
    have hnδ : (0 : ℝ) ≤ (n : ℝ) * (‖c‖ * (‖c‖ - 2)) :=
      mul_nonneg (Nat.cast_nonneg n) hδ0
    have hu_ge : ‖c‖ ≤ ‖orbit c 0 (n + 1)‖ := by linarith
    have hv : orbit c 0 (n + 1 + 1) = orbit c 0 (n + 1) ^ 2 + c := by
      rw [orbit_succ]
      rfl
    have hnorm : ‖orbit c 0 (n + 1)‖ ^ 2 ≤ ‖orbit c 0 (n + 1 + 1)‖ + ‖c‖ := by
      rw [← norm_pow]
      have hsub : orbit c 0 (n + 1) ^ 2 = orbit c 0 (n + 1 + 1) - c := by
        rw [hv]
        ring
      rw [hsub]
      exact norm_sub_le _ _
    have hkey : ‖orbit c 0 (n + 1)‖ + ‖c‖ * (‖c‖ - 2)
        ≤ ‖orbit c 0 (n + 1)‖ ^ 2 - ‖c‖ := by
      nlinarith [mul_nonneg (sub_nonneg.2 hu_ge) (by linarith : (0 : ℝ) ≤ ‖orbit c 0 (n + 1)‖ + ‖c‖ - 1)]
    push_cast
    nlinarith [ih, hkey, hnorm]

/-- A complex parameter of modulus greater than `2` is outside the Mandelbrot set. -/
lemma not_boundedOrbit_of_two_lt_norm (c : ℂ) (hc : 2 < ‖c‖) : ¬ boundedOrbit c 0 := by
  rintro ⟨M, hM⟩
  have hδpos : 0 < ‖c‖ * (‖c‖ - 2) := mul_pos (by linarith) (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (M / (‖c‖ * (‖c‖ - 2)))
  have h1 := norm_orbit_ge_of_two_lt_norm c hc n
  have h2 := hM (n + 1)
  rw [div_lt_iff₀ hδpos] at hn
  nlinarith [norm_nonneg c]

/-- For real `x > 1/4` the real orbit of `0` grows linearly. -/
lemma realOrbit_ge_of_quarter_lt (x : ℝ) (n : ℕ) :
    (n : ℝ) * (x - 1 / 4) ≤ realOrbit x n := by
  induction n with
  | zero => simp [realOrbit]
  | succ n ih =>
    rw [realOrbit]
    push_cast
    nlinarith [sq_nonneg (realOrbit x n - 1 / 2)]

lemma not_boundedOrbit_of_quarter_lt (x : ℝ) (hx : 1 / 4 < x) :
    ¬ boundedOrbit (x : ℂ) 0 := by
  rintro ⟨M, hM⟩
  have hδ : 0 < x - 1 / 4 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (M / (x - 1 / 4))
  have h1 := realOrbit_ge_of_quarter_lt x n
  have h2 := hM n
  rw [orbit_ofReal, Complex.norm_real, Real.norm_eq_abs] at h2
  rw [div_lt_iff₀ hδ] at hn
  have h4 : realOrbit x n ≤ |realOrbit x n| := le_abs_self _
  linarith

lemma sqrt_one_sub_four_mul_le_three {x : ℝ} (hx : -2 ≤ x) :
    Real.sqrt (1 - 4 * x) ≤ 3 := by
  have h9 : 1 - 4 * x ≤ 9 := by linarith
  calc Real.sqrt (1 - 4 * x) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt h9
    _ = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- For `x ∈ [-2, 1/4]`, the real orbit of `0` stays in `[-β, β]`, where
`β = (1 + √(1 - 4x))/2` satisfies `β² + x = β`. -/
lemma realOrbit_mem_Icc_of_mem_Icc (x : ℝ) (h1 : -2 ≤ x) (h2 : x ≤ 1 / 4) (n : ℕ) :
    -((1 + Real.sqrt (1 - 4 * x)) / 2) ≤ realOrbit x n ∧
      realOrbit x n ≤ (1 + Real.sqrt (1 - 4 * x)) / 2 := by
  have hs0 : 0 ≤ Real.sqrt (1 - 4 * x) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (1 - 4 * x) ^ 2 = 1 - 4 * x := Real.sq_sqrt (by linarith)
  have hs3 : Real.sqrt (1 - 4 * x) ≤ 3 := sqrt_one_sub_four_mul_le_three h1
  set s := Real.sqrt (1 - 4 * x) with hs
  set β := (1 + s) / 2 with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hfix : β ^ 2 + x = β := by
    rw [hβ]
    linear_combination (1 / 4 : ℝ) * hs2
  have hlow : -β ≤ x := by
    rw [hβ]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - s) (by linarith : (0 : ℝ) ≤ 1 + s)]
  induction n with
  | zero =>
    have h0 : realOrbit x 0 = 0 := rfl
    rw [h0]
    exact ⟨by linarith, hβ0⟩
  | succ n ih =>
    rw [realOrbit]
    obtain ⟨hl, hu⟩ := ih
    constructor
    · nlinarith [sq_nonneg (realOrbit x n)]
    · have habs : (realOrbit x n) ^ 2 ≤ β ^ 2 := by nlinarith
      linarith

lemma boundedOrbit_ofReal_of_mem_Icc (x : ℝ) (h1 : -2 ≤ x) (h2 : x ≤ 1 / 4) :
    boundedOrbit (x : ℂ) 0 := by
  refine ⟨2, fun n => ?_⟩
  rw [orbit_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hs3 : Real.sqrt (1 - 4 * x) ≤ 3 := sqrt_one_sub_four_mul_le_three h1
  obtain ⟨hl, hu⟩ := realOrbit_mem_Icc_of_mem_Icc x h1 h2 n
  constructor <;> linarith

/-- **Real slice of the Mandelbrot set.** A real parameter `x` lies in the Mandelbrot
set exactly when `-2 ≤ x ≤ 1/4`. -/
theorem ofReal_mem_mandelbrotSet_iff (x : ℝ) :
    (x : ℂ) ∈ MLC.Quadratic.MandelbrotSet ↔ -2 ≤ x ∧ x ≤ 1 / 4 := by
  refine ⟨fun hx => ?_, fun hx => boundedOrbit_ofReal_of_mem_Icc x hx.1 hx.2⟩
  by_contra hcon
  rcases not_and_or.mp hcon with h | h
  · push_neg at h
    refine not_boundedOrbit_of_two_lt_norm (x : ℂ) ?_ hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  · push_neg at h
    exact not_boundedOrbit_of_quarter_lt x h hx

end MLC.Quadratic.RealSlice
