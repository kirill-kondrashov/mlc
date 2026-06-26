/-
Copyright (c) 2025 The MLC Project Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mlc.Quadratic.Complex.Bottcher.GreenFunctionRayInversion

/-!
# Orbit Norm Ratio Growth Along Rays for f₂(z) = z² + 2

This file proves that for points on the same ray with t₂ > t₁ > 4,
the orbit norm ratio `‖orbit 2 (t₂·u) n‖ / ‖orbit 2 (t₁·u) n‖` tends to infinity.

## Main results

* `norm_fc_two_sq_strictMono_along_ray`: |fc(t₂·u)|² > |fc(t₁·u)|² for t₂ > t₁ > 4
* `norm_orbit_two_ratio_tendsto_atTop_along_ray`: ratio → ∞ along rays

## Key insight

For arbitrary z₁, z₂ with |z₂| > |z₁| > 4, orbit norms need NOT stay ordered
(counterexample: z₁ = 5, z₂ = 5.01i gives |fc(z₂)| < |fc(z₁)|).

For points **on the same ray** (z₁ = t₁·u, z₂ = t₂·u with ‖u‖ = 1), we use:
  |fc(t·u)|² = |t²·u² + 2|² = t⁴ + 4t²·Re(u²) + 4
which is strictly increasing in t for t > 2 (derivative
4t³ + 8t·Re(u²) > 0), together with the Green-function scaling/bounded-error
estimates along orbits.

-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric Real
open scoped Topology

namespace OrbitNormRatio

/-! ## Norm ordering along rays -/

/-- For fc(z) = z² + c, the squared norm |fc(t·u)|² is a polynomial in t².
Specifically, |fc(t·u)|² = t⁴ + 4t²·Re(u²) + 4|u|² + 4Re(c·ū²·t²) + 4Re(c) + |c|²
For c = 2 and ‖u‖ = 1: |fc(t·u)|² = t⁴ + 4t²·Re(u²) + 4 -/
private lemma norm_fc_two_sq_eq (t : ℝ) (u : ℂ) (hu : ‖u‖ = 1) :
    ‖fc (2 : ℂ) ((t : ℂ) * u)‖^2 = t^4 + 4 * t^2 * (u^2).re + 4 := by
  -- fc(t·u) = (t·u)² + 2 = t²·u² + 2
  have heq : fc (2 : ℂ) ((t : ℂ) * u) = (t : ℂ)^2 * u^2 + 2 := by simp only [fc]; ring
  rw [heq]
  -- |z|² = z.re² + z.im²
  have norm_sq_expand : ∀ z : ℂ, ‖z‖^2 = z.re^2 + z.im^2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [norm_sq_expand]
  -- Let w = t²·u² + 2
  set w := (t : ℂ)^2 * u^2 + 2 with hw_def
  -- Compute w.re and w.im using sq_abs for (t : ℂ)^2
  have ht2_eq : (t : ℂ)^2 = (t * t : ℂ) := by ring
  have ht2_re : ((t : ℂ)^2).re = t^2 := by
    rw [ht2_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring
  have ht2_im : ((t : ℂ)^2).im = 0 := by
    rw [ht2_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]; ring
  have two_re : (2 : ℂ).re = 2 := Complex.natCast_re 2
  have two_im : (2 : ℂ).im = 0 := Complex.natCast_im 2
  have hw_re : w.re = t^2 * (u^2).re + 2 := by
    simp only [hw_def, Complex.add_re, Complex.mul_re, ht2_re, ht2_im, two_re]; ring
  have hw_im : w.im = t^2 * (u^2).im := by
    simp only [hw_def, Complex.add_im, Complex.mul_im, ht2_re, ht2_im, zero_mul, add_zero, two_im]
  rw [hw_re, hw_im]
  -- Since |u| = 1, |u²| = |u|² = 1, so Re(u²)² + Im(u²)² = 1
  have hu2_norm : Complex.normSq (u^2) = 1 := by
    rw [map_pow, ← Complex.sq_norm, hu]; norm_num
  have h_expand : (u^2).re^2 + (u^2).im^2 = 1 := by
    have := Complex.normSq_apply (u^2)
    rw [hu2_norm] at this
    linarith
  -- Expand: (t²·Re(u²) + 2)² + (t²·Im(u²))² = t⁴ + 4t²·Re(u²) + 4
  nlinarith [sq_nonneg (u^2).re, sq_nonneg (u^2).im, h_expand, sq_nonneg t, sq_nonneg (t^2)]

/-- The squared norm |fc(t·u)|² is strictly increasing in t for t > 2 and ‖u‖ = 1.
This follows from the derivative being positive: d/dt |fc(t·u)|² = 4t³ + 8t·Re(u²) > 0 for t > 2. -/
lemma norm_fc_two_sq_strictMono_along_ray (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > 2) (ht₂ : t₁ < t₂) :
    ‖fc (2 : ℂ) ((t₁ : ℂ) * u)‖^2 < ‖fc (2 : ℂ) ((t₂ : ℂ) * u)‖^2 := by
  rw [norm_fc_two_sq_eq t₁ u hu, norm_fc_two_sq_eq t₂ u hu]
  -- Need: t₁⁴ + 4t₁²·Re(u²) + 4 < t₂⁴ + 4t₂²·Re(u²) + 4
  -- i.e., (t₂⁴ - t₁⁴) + 4(t₂² - t₁²)·Re(u²) > 0
  -- i.e., (t₂² - t₁²)(t₂² + t₁² + 4·Re(u²)) > 0
  have hdiff : t₂^2 - t₁^2 > 0 := by nlinarith
  have hsum : t₂^2 + t₁^2 + 4 * (u^2).re > 0 := by
    have hre : (u^2).re ≥ -1 := by
      have h := Complex.abs_re_le_norm (u^2)
      have hnorm : ‖u^2‖ = 1 := by rw [norm_pow, hu, one_pow]
      have habs : |((u^2).re)| ≤ 1 := by rw [← hnorm]; exact h
      linarith [neg_abs_le ((u^2).re)]
    have ht : t₂^2 + t₁^2 > 8 := by nlinarith
    linarith
  nlinarith

/-- For s > 4 and ‖v‖ = 1, the squared norm is bounded by worst-case values. -/
private lemma norm_fc_two_sq_bounds (s : ℝ) (v : ℂ) (_hs : s > 4) (hv : ‖v‖ = 1) :
    s^4 - 4 * s^2 + 4 ≤ ‖fc (2 : ℂ) ((s : ℂ) * v)‖^2 ∧
    ‖fc (2 : ℂ) ((s : ℂ) * v)‖^2 ≤ s^4 + 4 * s^2 + 4 := by
  rw [norm_fc_two_sq_eq s v hv]
  have hre_bdd : |((v^2).re)| ≤ 1 := by
    have h := Complex.abs_re_le_norm (v^2)
    have hnorm : ‖v^2‖ = 1 := by rw [norm_pow, hv, one_pow]
    rw [← hnorm]; exact h
  constructor <;> nlinarith [abs_le.mp hre_bdd]

/-- When s₂² - s₁² > 4, the squared norm comparison holds for any unit directions.
This is the "worst-case" comparison that works regardless of directions. -/
private lemma norm_fc_two_sq_compare_large_gap (s₁ s₂ : ℝ) (v₁ v₂ : ℂ)
    (hs₁ : s₁ > 4) (hs₂ : s₂ > s₁) (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1)
    (hgap : s₂^2 - s₁^2 > 4) :
    ‖fc (2 : ℂ) ((s₁ : ℂ) * v₁)‖^2 < ‖fc (2 : ℂ) ((s₂ : ℂ) * v₂)‖^2 := by
  have hs₂_gt_4 : s₂ > 4 := by linarith
  have ⟨h1_lo, h1_hi⟩ := norm_fc_two_sq_bounds s₁ v₁ hs₁ hv₁
  have ⟨h2_lo, h2_hi⟩ := norm_fc_two_sq_bounds s₂ v₂ hs₂_gt_4 hv₂
  -- Need: s₂⁴ - 4s₂² + 4 > s₁⁴ + 4s₁² + 4
  -- i.e., s₂⁴ - s₁⁴ > 4(s₂² + s₁²)
  -- i.e., (s₂² - s₁²)(s₂² + s₁²) > 4(s₂² + s₁²)
  -- i.e., s₂² - s₁² > 4 (which is hgap)
  have hsum_pos : s₂^2 + s₁^2 > 0 := by nlinarith
  have h_key : s₂^4 - 4 * s₂^2 + 4 > s₁^4 + 4 * s₁^2 + 4 := by
    have h1 : s₂^4 - s₁^4 = (s₂^2 - s₁^2) * (s₂^2 + s₁^2) := by ring
    have h2 : s₂^4 - s₁^4 > 4 * (s₂^2 + s₁^2) := by
      rw [h1]; exact mul_lt_mul_of_pos_right hgap hsum_pos
    linarith
  linarith

/-- For s₂ > s₁ > 4, the squared norm ratio after fc is bounded below.
This shows the ratio grows multiplicatively with each iteration. -/
private lemma norm_fc_two_ratio_sq_lower_bound (s₁ s₂ : ℝ) (v₁ v₂ : ℂ)
    (hs₁ : s₁ > 4) (hs₂ : s₂ > s₁) (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1) :
    ‖fc (2 : ℂ) ((s₂ : ℂ) * v₂)‖^2 > s₂^2 * (s₂^2 - 4) ∧
    ‖fc (2 : ℂ) ((s₁ : ℂ) * v₁)‖^2 < s₁^2 * (s₁^2 + 5) := by
  have hs₂_gt_4 : s₂ > 4 := by linarith
  have ⟨h1_lo, h1_hi⟩ := norm_fc_two_sq_bounds s₁ v₁ hs₁ hv₁
  have ⟨h2_lo, h2_hi⟩ := norm_fc_two_sq_bounds s₂ v₂ hs₂_gt_4 hv₂
  constructor
  · -- Lower bound on numerator: ‖fc(s₂·v₂)‖² ≥ s₂⁴ - 4s₂² + 4 > s₂²(s₂² - 4)
    nlinarith
  · -- Upper bound on denominator: ‖fc(s₁·v₁)‖² ≤ s₁⁴ + 4s₁² + 4 < s₁²(s₁² + 5)
    nlinarith

/-- Orbit norms stay above 4 for c=2 and starting point on ray with t > 4. -/
private lemma norm_orbit_two_ray_gt_four (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : t > 4) (n : ℕ) :
    ‖orbit (2 : ℂ) ((t : ℂ) * u) n‖ > 4 := by
  have hnorm : ‖(t : ℂ) * u‖ = t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
  induction n with
  | zero => simp only [Quadratic.orbit_zero, hnorm]; exact ht
  | succ n ih =>
    rw [Quadratic.orbit_succ]
    have h := norm_fc_ge_norm_sq_sub_norm_c (2 : ℂ) (orbit (2 : ℂ) ((t : ℂ) * u) n)
    simp only [Complex.norm_two] at h
    have horb_pos : ‖orbit (2 : ℂ) ((t : ℂ) * u) n‖ > 0 := by linarith
    nlinarith [sq_pos_of_pos horb_pos]

/-- Helper: orbit of t·u can be written as t_n · u_n for some t_n > 4 and ‖u_n‖ = 1 -/
private lemma orbit_ray_decomposition (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : t > 4) (n : ℕ) :
    ∃ (tₙ : ℝ) (uₙ : ℂ), tₙ > 4 ∧ ‖uₙ‖ = 1 ∧ orbit (2 : ℂ) ((t : ℂ) * u) n = (tₙ : ℂ) * uₙ := by
  induction n with
  | zero =>
    refine ⟨t, u, ht, hu, ?_⟩
    simp only [Quadratic.orbit_zero]
  | succ n ih =>
    obtain ⟨tₙ, uₙ, htₙ, huₙ, heq⟩ := ih
    simp only [Quadratic.orbit_succ, heq]
    -- fc(tₙ·uₙ) = tₙ²·uₙ² + 2
    have hfc : fc (2 : ℂ) ((tₙ : ℂ) * uₙ) = (tₙ : ℂ)^2 * uₙ^2 + 2 := by simp [fc]; ring
    -- The norm of this is > 4
    have hnorm_fc : ‖fc (2 : ℂ) ((tₙ : ℂ) * uₙ)‖ > 4 := by
      have h := norm_fc_ge_norm_sq_sub_norm_c (2 : ℂ) ((tₙ : ℂ) * uₙ)
      simp only [Complex.norm_two] at h
      have hnorm_in : ‖(tₙ : ℂ) * uₙ‖ = tₙ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), huₙ, mul_one]
      rw [hnorm_in] at h
      nlinarith [sq_pos_of_pos (by linarith : tₙ > 0)]
    -- Write fc(tₙ·uₙ) = t_{n+1} · u_{n+1}
    let t_next := ‖fc (2 : ℂ) ((tₙ : ℂ) * uₙ)‖
    have ht_next_pos : t_next > 0 := by linarith
    let u_next := fc (2 : ℂ) ((tₙ : ℂ) * uₙ) / t_next
    have hu_next : ‖u_next‖ = 1 := by
      simp only [u_next, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_next_pos]
      exact div_self (ne_of_gt ht_next_pos)
    have heq_next : fc (2 : ℂ) ((tₙ : ℂ) * uₙ) = (t_next : ℂ) * u_next := by
      simp only [u_next, t_next]
      rw [mul_div_cancel₀]
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt ht_next_pos
    exact ⟨t_next, u_next, hnorm_fc, hu_next, heq_next⟩

/-- For points on the same ray with t₂ > t₁ > 4, the orbit norm ratio tends to infinity. -/
lemma norm_orbit_two_ratio_tendsto_atTop_along_ray (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₁ < t₂) :
    Tendsto (fun n : ℕ => ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ / ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖)
      atTop atTop := by
  have ht₂_gt_4 : t₂ > 4 := by linarith
  -- Norms of starting points
  have hnorm₁ : ‖(t₁ : ℂ) * u‖ = t₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
  have hnorm₂ : ‖(t₂ : ℂ) * u‖ = t₂ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
  have hz₁_gt_4 : ‖(t₁ : ℂ) * u‖ > 4 := by rw [hnorm₁]; exact ht₁
  have hz₂_gt_4 : ‖(t₂ : ℂ) * u‖ > 4 := by rw [hnorm₂]; exact ht₂_gt_4
  -- Use the Green function O(1) bound
  set M := 2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ))^2 with hM_def
  have hbdd₁ : ∀ n, |Real.log ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ -
      2^n * green_function (2 : ℂ) ((t₁ : ℂ) * u)| ≤ M := by
    intro n
    have := GreenFunctionRayInversion.log_norm_orbit_two_eq_green_scaled ((t₁ : ℂ) * u) hz₁_gt_4 n
    simp only [hM_def]; exact this
  have hbdd₂ : ∀ n, |Real.log ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ -
      2^n * green_function (2 : ℂ) ((t₂ : ℂ) * u)| ≤ M := by
    intro n
    have := GreenFunctionRayInversion.log_norm_orbit_two_eq_green_scaled ((t₂ : ℂ) * u) hz₂_gt_4 n
    simp only [hM_def]; exact this
  set G₁ := green_function (2 : ℂ) ((t₁ : ℂ) * u)
  set G₂ := green_function (2 : ℂ) ((t₂ : ℂ) * u)
  have hG_lt : G₁ < G₂ := by
    simpa [G₁, G₂] using
      GreenFunctionRayInversion.green_function_strictMono_along_ray_two u hu ht₁ ht₂
  have hG_pos : G₂ - G₁ > 0 := by linarith
  have hlog_tends : Tendsto (fun n : ℕ => Real.log (‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ /
      ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖)) atTop atTop := by
    have hdiff_bound : ∀ n, Real.log ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ -
        Real.log ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ ≥ 2^n * (G₂ - G₁) - 2 * M := fun n => by
      have h1 := hbdd₁ n
      have h2 := hbdd₂ n
      rw [abs_le] at h1 h2
      linarith
    have h2pow : Tendsto (fun n : ℕ => (2 : ℝ)^n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hprod : Tendsto (fun n : ℕ => (2 : ℝ)^n * (G₂ - G₁)) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hG_pos h2pow
    have htend : Tendsto (fun n : ℕ => 2^n * (G₂ - G₁) - 2 * M) atTop atTop :=
      Filter.Tendsto.atTop_add hprod tendsto_const_nhds
    apply Filter.tendsto_atTop_mono (fun n => ?_) htend
    have h1_pos : ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ > 0 := by
      linarith [norm_orbit_two_ray_gt_four u hu t₁ ht₁ n]
    have h2_pos : ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ > 0 := by
      linarith [norm_orbit_two_ray_gt_four u hu t₂ ht₂_gt_4 n]
    rw [Real.log_div h2_pos.ne' h1_pos.ne']
    exact hdiff_bound n
  exact Real.tendsto_exp_atTop.comp hlog_tends |>.congr fun n => by
    have h1_pos : ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ > 0 := by
      linarith [norm_orbit_two_ray_gt_four u hu t₁ ht₁ n]
    have h2_pos : ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ > 0 := by
      linarith [norm_orbit_two_ray_gt_four u hu t₂ ht₂_gt_4 n]
    exact Real.exp_log (div_pos h2_pos h1_pos)

/-- Per-step two-sided bound on the squared orbit norm along a ray at `c = 2`. -/
private lemma orbit_two_norm_sq_step (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : t > 4) (n : ℕ) :
    ‖orbit (2 : ℂ) ((t : ℂ) * u) (n + 1)‖ ^ 2 ≤
        ‖orbit (2 : ℂ) ((t : ℂ) * u) n‖ ^ 4 + 4 * ‖orbit (2 : ℂ) ((t : ℂ) * u) n‖ ^ 2 + 4 ∧
      ‖orbit (2 : ℂ) ((t : ℂ) * u) (n + 1)‖ ^ 2 ≥
        ‖orbit (2 : ℂ) ((t : ℂ) * u) n‖ ^ 4 - 4 * ‖orbit (2 : ℂ) ((t : ℂ) * u) n‖ ^ 2 + 4 := by
  obtain ⟨sₙ, vₙ, hsₙ, hvₙ, heq⟩ := orbit_ray_decomposition u hu t ht n
  have hsv : ‖(↑sₙ : ℂ) * vₙ‖ = sₙ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hvₙ, mul_one]
  obtain ⟨lo, hi⟩ := norm_fc_two_sq_bounds sₙ vₙ hsₙ hvₙ
  rw [Quadratic.orbit_succ, heq, hsv]
  exact ⟨hi, lo⟩

/-- The core multiplicative-growth polynomial inequality behind the large-ratio island:
with `A = ‖aₙ‖²`, `B = ‖bₙ‖²`, `A > 16` and `B ≥ 2A`, the squared ratio grows by at
least a factor `21/16` per step. -/
private lemma large_ratio_poly (A B : ℝ) (hA : A > 16) (hB : B ≥ 2 * A) :
    16 * A * (B ^ 2 - 4 * B + 4) ≥ 21 * B * (A ^ 2 + 4 * A + 4) := by
  nlinarith [sq_nonneg (B - 2 * A), mul_pos (by linarith : (0:ℝ) < A) (by linarith : (0:ℝ) < B),
    mul_nonneg (by linarith : (0:ℝ) ≤ B - 2 * A) (by linarith : (0:ℝ) ≤ A),
    mul_nonneg (by linarith : (0:ℝ) ≤ B - 2 * A) (by linarith : (0:ℝ) ≤ B),
    mul_pos (by linarith : (0:ℝ) < A) (by linarith : (0:ℝ) < A)]

/-- Pure real-sequence engine behind the large-ratio island.  For opaque positive
sequences `a, b` obeying the crude one-step squared-norm bounds and starting with
squared ratio `≥ 2`, the squared ratio dominates the geometric sequence `2·(21/16)ⁿ`.
Keeping `a, b` opaque prevents `nlinarith` from unfolding the orbit recursion. -/
private lemma ratio_geom_lower (a b : ℕ → ℝ)
    (ha4 : ∀ n, a n > 4) (hb4 : ∀ n, b n > 4)
    (hUB : ∀ n, (a (n + 1)) ^ 2 ≤ (a n) ^ 4 + 4 * (a n) ^ 2 + 4)
    (hLB : ∀ n, (b (n + 1)) ^ 2 ≥ (b n) ^ 4 - 4 * (b n) ^ 2 + 4)
    (h0 : (b 0 / a 0) ^ 2 ≥ 2) :
    ∀ n, (b n / a n) ^ 2 ≥ 2 * (21 / 16) ^ n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hAn : a n > 4 := ha4 n
    have hBn : b n > 4 := hb4 n
    have hApos : (0:ℝ) < a n := by linarith
    have hBpos : (0:ℝ) < b n := by linarith
    -- From ih, the current squared ratio is ≥ 2, giving B ≥ 2A.
    have hgeom : (2:ℝ) * (21 / 16) ^ n ≥ 2 := by
      have : (21 / 16 : ℝ) ^ n ≥ 1 := one_le_pow₀ (by norm_num)
      linarith
    have hrn2 : (b n / a n) ^ 2 ≥ 2 := le_trans hgeom ih
    have hBA : (b n) ^ 2 ≥ 2 * (a n) ^ 2 := by
      rw [div_pow, ge_iff_le, le_div_iff₀ (by positivity)] at hrn2; linarith
    set A := (a n) ^ 2 with hA_def
    set B := (b n) ^ 2 with hB_def
    have hAgt : A > 16 := by rw [hA_def]; nlinarith [hAn]
    have hBgt : B ≥ 2 * A := by rw [hA_def, hB_def]; linarith
    have hpoly := large_ratio_poly A B hAgt hBgt
    have hApos2 : (0:ℝ) < A := by rw [hA_def]; exact pow_pos hApos 2
    have hBpos2 : (0:ℝ) < B := by rw [hB_def]; exact pow_pos hBpos 2
    have haq : (a n) ^ 4 = A ^ 2 := by rw [hA_def]; ring
    have hbq : (b n) ^ 4 = B ^ 2 := by rw [hB_def]; ring
    have hLBb' : (b (n + 1)) ^ 2 ≥ B ^ 2 - 4 * B + 4 := by rw [← hbq]; linarith [hLB n]
    have hUBa' : (a (n + 1)) ^ 2 ≤ A ^ 2 + 4 * A + 4 := by rw [← haq]; linarith [hUB n]
    -- Abstract level-(n+1) squared norms into opaque reals so `nlinarith` stays fast.
    set P := (b (n + 1)) ^ 2 with hP_def
    set Q := (a (n + 1)) ^ 2 with hQ_def
    have hQpos : (0:ℝ) < Q := by rw [hQ_def]; exact pow_pos (by linarith [ha4 (n + 1)]) 2
    -- Cross-multiplied per-step growth: 16·P·A ≥ 21·B·Q.
    have hcross : 16 * P * A ≥ 21 * B * Q := by
      have h1 : 16 * P * A ≥ 16 * (B ^ 2 - 4 * B + 4) * A :=
        by nlinarith [mul_nonneg (by linarith [hLBb'] : (0:ℝ) ≤ P - (B ^ 2 - 4 * B + 4)) hApos2.le]
      have h2 : 21 * B * Q ≤ 21 * B * (A ^ 2 + 4 * A + 4) :=
        by nlinarith [mul_nonneg hBpos2.le (by linarith [hUBa'] : (0:ℝ) ≤ (A ^ 2 + 4 * A + 4) - Q)]
      nlinarith [h1, h2, hpoly]
    have hstep : P / Q ≥ (21 / 16) * (B / A) := by
      rw [ge_iff_le, show (21:ℝ) / 16 * (B / A) = (21 * B) / (16 * A) by ring,
        div_le_div_iff₀ (by positivity) hQpos]
      nlinarith [hcross]
    have hih' : B / A ≥ 2 * (21 / 16) ^ n := by
      rw [hB_def, hA_def, ← div_pow]; exact ih
    rw [div_pow, ← hP_def, ← hQ_def]
    calc P / Q
        ≥ (21 / 16) * (B / A) := hstep
      _ ≥ (21 / 16) * (2 * (21 / 16) ^ n) := by
            have := mul_le_mul_of_nonneg_left hih' (by norm_num : (0:ℝ) ≤ 21 / 16); linarith
      _ = 2 * (21 / 16) ^ (n + 1) := by ring

/-- **Large-ratio orbit blow-up (direction-agnostic, Green-free).**
For points on the same ray at `c = 2` with `t₁ > 4` and initial squared ratio
`t₂² ≥ 2 t₁²`, the orbit-norm ratio tends to `∞`.  Unlike
`norm_orbit_two_ratio_tendsto_atTop_along_ray`, this does **not** invoke Green
monotonicity: it uses only the crude norm recursion `‖z²+2‖² ∈ [‖z‖⁴−4‖z‖²+4, …]`,
which self-amplifies above the ratio threshold `≈ 1.231` (here `√2 > 1.231`). -/
lemma norm_orbit_two_ratio_tendsto_atTop_along_ray_of_large_ratio
    (u : ℂ) (hu : ‖u‖ = 1) {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₂ > 4)
    (hratio : 2 * t₁ ^ 2 ≤ t₂ ^ 2) :
    Tendsto (fun n : ℕ => ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ / ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖)
      atTop atTop := by
  have ha4 : ∀ n, ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ > 4 :=
    fun n => norm_orbit_two_ray_gt_four u hu t₁ ht₁ n
  have hb4 : ∀ n, ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ > 4 :=
    fun n => norm_orbit_two_ray_gt_four u hu t₂ ht₂ n
  have hUB : ∀ n, ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) (n + 1)‖ ^ 2 ≤
      ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ ^ 4 + 4 * ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ ^ 2 + 4 :=
    fun n => (orbit_two_norm_sq_step u hu t₁ ht₁ n).1
  have hLB : ∀ n, ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) (n + 1)‖ ^ 2 ≥
      ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ ^ 4 - 4 * ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ ^ 2 + 4 :=
    fun n => (orbit_two_norm_sq_step u hu t₂ ht₂ n).2
  have h0 : (‖orbit (2 : ℂ) ((t₂ : ℂ) * u) 0‖ / ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) 0‖) ^ 2 ≥ 2 := by
    rw [Quadratic.orbit_zero, Quadratic.orbit_zero]
    have e1 : ‖(t₁ : ℂ) * u‖ = t₁ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
    have e2 : ‖(t₂ : ℂ) * u‖ = t₂ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
    rw [e1, e2, div_pow, ge_iff_le, le_div_iff₀ (by positivity)]
    linarith [hratio]
  have hSbound := ratio_geom_lower _ _ ha4 hb4 hUB hLB h0
  -- The squared ratio tends to ∞, hence the ratio itself does.
  have hpow : Tendsto (fun n : ℕ => (21 / 16 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hgeom_top : Tendsto (fun n : ℕ => 2 * (21 / 16 : ℝ) ^ n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hpow
  have hsqrt_top : Tendsto (fun n : ℕ => Real.sqrt (2 * (21 / 16 : ℝ) ^ n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hgeom_top
  refine tendsto_atTop_mono (fun n => ?_) hsqrt_top
  have hx : (0:ℝ) ≤ ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ / ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ :=
    le_of_lt (div_pos (by linarith [hb4 n]) (by linarith [ha4 n]))
  calc Real.sqrt (2 * (21 / 16 : ℝ) ^ n)
      ≤ Real.sqrt ((‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ / ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖) ^ 2) :=
        Real.sqrt_le_sqrt (hSbound n)
    _ = ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ / ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ := Real.sqrt_sq hx

/-- **Green strict monotonicity along a ray at `c = 2`, large-ratio regime.**
Wiring the constructive, Green-free island
`norm_orbit_two_ratio_tendsto_atTop_along_ray_of_large_ratio` through the reduction
lemma `green_function_lt_of_escaping_of_orbit_ratio_tendsto_atTop`.  Covers the
large-ratio case `t₂² ≥ 2 t₁²` (`t₂ ≳ 1.41·t₁`) with no appeal to the seam axiom. -/
lemma green_function_strictMono_along_ray_two_of_large_ratio
    (u : ℂ) (hu : ‖u‖ = 1) {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₂ > 4)
    (hratio : 2 * t₁ ^ 2 ≤ t₂ ^ 2) :
    Quadratic.green_function (2 : ℂ) ((t₁ : ℂ) * u) <
      Quadratic.green_function (2 : ℂ) ((t₂ : ℂ) * u) := by
  have hesc_two : Quadratic.escape_bound (2 : ℂ) = 3 := by
    have h2norm : ‖(2 : ℂ)‖ = 2 := by rw [Complex.norm_ofNat]
    rw [Quadratic.escape_bound_eq_max, h2norm]; norm_num
  have hesc₁ : ∀ n, ‖orbit (2 : ℂ) ((t₁ : ℂ) * u) n‖ > Quadratic.escape_bound (2 : ℂ) := by
    intro n; rw [hesc_two]; linarith [norm_orbit_two_ray_gt_four u hu t₁ ht₁ n]
  have hesc₂ : ∀ n, ‖orbit (2 : ℂ) ((t₂ : ℂ) * u) n‖ > Quadratic.escape_bound (2 : ℂ) := by
    intro n; rw [hesc_two]; linarith [norm_orbit_two_ray_gt_four u hu t₂ ht₂ n]
  exact GreenFunctionRayInversion.green_function_strictMono_along_ray_of_orbit_ratio
    (2 : ℂ) u hesc₁ hesc₂
    (norm_orbit_two_ratio_tendsto_atTop_along_ray_of_large_ratio u hu ht₁ ht₂ hratio)

end OrbitNormRatio

end MLC