import Yoccoz.Quadratic.Complex.Basic

/-!
# Two exact Julia sets of the quadratic family

Two classical examples from Milnor's *Dynamics in One Complex Variable*:

* for `c = 0`, the filled Julia set is the closed unit disk and the Julia set is the unit circle;
* for `c = -2`, the filled Julia set is the real segment `[-2, 2]` (Chebyshev polynomials), and
  the Julia set is the same segment.

The second computation uses the Joukowski parametrization `z = w + w⁻¹`, for which the
orbit of `z` under `t ↦ t² - 2` is `w^(2^n) + w⁻¹^(2^n)`.
-/

namespace MLC.Quadratic.Examples

open Complex Metric Set

noncomputable section

/-! ### The parameter `c = 0` -/

lemma orbit_zero_param (z : ℂ) (n : ℕ) : MLC.Quadratic.orbit 0 z n = z ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [MLC.Quadratic.orbit_succ, ih]
    show (z ^ 2 ^ n) ^ 2 + 0 = z ^ 2 ^ (n + 1)
    rw [add_zero, ← pow_mul, pow_succ]

theorem filledJulia_zero : MLC.Quadratic.K 0 = closedBall (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨M, hM⟩
    by_contra hz
    rw [mem_closedBall_zero_iff, not_le] at hz
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hz
    have h1 := hM n
    rw [orbit_zero_param, norm_pow] at h1
    have h2 : ‖z‖ ^ n ≤ ‖z‖ ^ 2 ^ n :=
      pow_le_pow_right₀ hz.le (Nat.lt_two_pow_self).le
    linarith
  · intro hz
    rw [mem_closedBall_zero_iff] at hz
    refine ⟨1, fun n => ?_⟩
    rw [orbit_zero_param, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz

theorem julia_zero : MLC.Quadratic.J 0 = sphere (0 : ℂ) 1 := by
  unfold MLC.Quadratic.J
  rw [filledJulia_zero, frontier_closedBall _ one_ne_zero]

/-! ### The parameter `c = -2` -/

lemma orbit_neg_two_real (x : ℝ) (hx : x ∈ Icc (-2 : ℝ) 2) (n : ℕ) :
    ∃ y : ℝ, y ∈ Icc (-2 : ℝ) 2 ∧ MLC.Quadratic.orbit (-2) (x : ℂ) n = (y : ℂ) := by
  induction n with
  | zero => exact ⟨x, hx, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyeq⟩ := ih
    refine ⟨y ^ 2 - 2, ⟨by nlinarith [sq_nonneg y, hy.1, hy.2], by nlinarith [hy.1, hy.2]⟩, ?_⟩
    rw [MLC.Quadratic.orbit_succ, hyeq]
    simp only [MLC.Quadratic.fc]
    push_cast
    ring

lemma boundedOrbit_neg_two_of_mem (x : ℝ) (hx : x ∈ Icc (-2 : ℝ) 2) :
    MLC.Quadratic.boundedOrbit (-2) (x : ℂ) := by
  refine ⟨2, fun n => ?_⟩
  obtain ⟨y, hy, hyeq⟩ := orbit_neg_two_real x hx n
  rw [hyeq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hy.1], hy.2⟩

/-- If `z = w + w⁻¹` with `|w| > 1`, the orbit of `z` under `t ↦ t² - 2` is unbounded. -/
lemma not_boundedOrbit_neg_two_of_root (z w : ℂ) (hz : z = w + w⁻¹) (hw : 1 < ‖w‖) :
    ¬ MLC.Quadratic.boundedOrbit (-2) z := by
  have hwne : w ≠ 0 := by
    rintro rfl
    norm_num at hw
  have hprod : w * w⁻¹ = 1 := mul_inv_cancel₀ hwne
  have key : ∀ n : ℕ, MLC.Quadratic.orbit (-2) z n = w ^ 2 ^ n + w⁻¹ ^ 2 ^ n := by
    intro n
    induction n with
    | zero => simp [hz]
    | succ n ih =>
      rw [MLC.Quadratic.orbit_succ, ih]
      show (w ^ 2 ^ n + w⁻¹ ^ 2 ^ n) ^ 2 + -2 = w ^ 2 ^ (n + 1) + w⁻¹ ^ 2 ^ (n + 1)
      have hab : w ^ 2 ^ n * w⁻¹ ^ 2 ^ n = 1 := by
        rw [← mul_pow, hprod, one_pow]
      rw [pow_succ 2 n, pow_mul, pow_mul]
      linear_combination 2 * hab
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M + 1) hw
  have h1 := hM n
  rw [key n] at h1
  have hb : ‖w⁻¹ ^ 2 ^ n‖ ≤ 1 := by
    rw [norm_pow, norm_inv]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hw.le)
  have htri : ‖w ^ 2 ^ n‖ ≤ ‖w ^ 2 ^ n + w⁻¹ ^ 2 ^ n‖ + ‖w⁻¹ ^ 2 ^ n‖ := by
    have := norm_sub_le (w ^ 2 ^ n + w⁻¹ ^ 2 ^ n) (w⁻¹ ^ 2 ^ n)
    simpa using this
  have hpow : ‖w‖ ^ n ≤ ‖w‖ ^ 2 ^ n := pow_le_pow_right₀ hw.le (Nat.lt_two_pow_self).le
  rw [norm_pow] at htri
  linarith

/-- If `w` has modulus `1`, then `w + w⁻¹` is real with absolute value at most `2`. -/
lemma add_inv_eq_ofReal_of_norm_eq_one (w : ℂ) (hw : ‖w‖ = 1) :
    ∃ x : ℝ, x ∈ Icc (-2 : ℝ) 2 ∧ w + w⁻¹ = (x : ℂ) := by
  have hnormSq : Complex.normSq w = 1 := by
    rw [Complex.normSq_eq_norm_sq, hw, one_pow]
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    rw [Complex.inv_def, hnormSq, inv_one, Complex.ofReal_one, mul_one]
  refine ⟨2 * w.re, ⟨?_, ?_⟩, ?_⟩
  · have := Complex.abs_re_le_norm w
    rw [hw] at this
    linarith [abs_le.mp this]
  · have := Complex.abs_re_le_norm w
    rw [hw] at this
    linarith [abs_le.mp this]
  · rw [hinv, Complex.add_conj]

/-- A complex number outside the real segment `[-2, 2]` is `w + w⁻¹` with `|w| > 1`. -/
lemma exists_joukowski_root_outside (z : ℂ) (hz : ∀ x ∈ Icc (-2 : ℝ) 2, z ≠ (x : ℂ)) :
    ∃ w : ℂ, z = w + w⁻¹ ∧ 1 < ‖w‖ := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 4) (by norm_num : 0 < 2)
  set w₁ := (z + s) / 2 with hw₁
  set w₂ := (z - s) / 2 with hw₂
  have hprod : w₁ * w₂ = 1 := by
    rw [hw₁, hw₂]
    linear_combination (-1 / 4 : ℂ) * hs
  have hsum : z = w₁ + w₂ := by
    rw [hw₁, hw₂]
    ring
  have hw₁ne : w₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  have hinv : w₂ = w₁⁻¹ := eq_inv_of_mul_eq_one_right hprod
  rcases lt_trichotomy ‖w₁‖ 1 with hlt | heq | hgt
  · -- then `w₂ = w₁⁻¹` has modulus greater than one
    refine ⟨w₂, ?_, ?_⟩
    · rw [hsum, hinv, inv_inv]
      ring
    · rw [hinv, norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hw₁ne)).mpr hlt
  · exfalso
    obtain ⟨x, hx, hxeq⟩ := add_inv_eq_ofReal_of_norm_eq_one w₁ heq
    apply hz x hx
    rw [hsum, hinv, hxeq]
  · refine ⟨w₁, ?_, hgt⟩
    rw [hsum, hinv]

theorem filledJulia_neg_two :
    MLC.Quadratic.K (-2) = (fun x : ℝ => (x : ℂ)) '' Icc (-2 : ℝ) 2 := by
  ext z
  constructor
  · intro hz
    by_contra hcon
    have hz' : ∀ x ∈ Icc (-2 : ℝ) 2, z ≠ (x : ℂ) := fun x hx h => hcon ⟨x, hx, h.symm⟩
    obtain ⟨w, hzw, hw⟩ := exists_joukowski_root_outside z hz'
    exact not_boundedOrbit_neg_two_of_root z w hzw hw hz
  · rintro ⟨x, hx, rfl⟩
    exact boundedOrbit_neg_two_of_mem x hx

theorem julia_neg_two :
    MLC.Quadratic.J (-2) = (fun x : ℝ => (x : ℂ)) '' Icc (-2 : ℝ) 2 := by
  unfold MLC.Quadratic.J
  rw [filledJulia_neg_two]
  have hclosed : IsClosed ((fun x : ℝ => (x : ℂ)) '' Icc (-2 : ℝ) 2) :=
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed
  have hint : interior ((fun x : ℝ => (x : ℂ)) '' Icc (-2 : ℝ) 2) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨x0, -, hx0⟩ := interior_subset hz
    have hzim : z.im = 0 := by rw [← hx0]; simp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
    set p : ℂ := z + ((ε / 2 : ℝ) : ℂ) * Complex.I with hp
    have hpball : p ∈ ball z ε := by
      rw [mem_ball, dist_eq_norm, hp, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos (by linarith)]
      linarith
    obtain ⟨x, -, hxp⟩ := hball hpball
    have him := congrArg Complex.im hxp
    rw [← hxp] at hpball
    simp [hp, hzim] at him
    linarith
  rw [frontier, hclosed.closure_eq, hint, diff_empty]

end

end MLC.Quadratic.Examples
