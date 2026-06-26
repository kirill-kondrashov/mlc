import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.Bottcher.BottcherMotion

/-!
# Parameter-holomorphy of the logarithmic-series Böttcher coordinate

This file discharges the **only missing field** of the near-infinity genuine
Böttcher parameter family (`GenuineBottcherNearInfinityParameterFamilyData`):
holomorphy of the Böttcher coordinate `φ_c(z) = logSeriesBottcherApprox c z` in
the *parameter* `c` on a fixed exterior region.

The four other fields (norm `> 1`, conjugacy `φ(f_c z) = φ(z)²`, fiber holomorphy
in `z`, and the `→ 1` normalisation at infinity) are already established in
`BottcherOutsidePlan.lean`.  Assembling all five yields the first genuine
(non-placeholder) construction of a Böttcher parameter family, feeding the
Böttcher/λ-lemma route to puzzle-boundary connectivity.

The parameter-holomorphy proof mirrors the fiberwise (`z`) proof:
`logSeriesBottcherApprox c z = z · exp (∑' n, nearOneLogCorrection c n z)`, each
term is holomorphic in `c` (the iterate `(quadratic_map c)^[n] z` is a polynomial
in `c`), and the series converges locally uniformly in `c` via the same summable
`(3/2)‖c‖(1/2)^{n+1}` majorant, made uniform over a parameter ball by `‖c‖ < ‖c₀‖ + r`.
-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric

/-- The `n`-th iterate `(quadratic_map c)^[n] z` is holomorphic in the parameter
`c` (for a fixed base point `z`).  Each `quadratic_map c w = w² + c` is affine in
`c`, so the claim follows by induction: `f_c^{n+1} z = (f_c^n z)² + c`. -/
lemma differentiable_iterate_param (z : ℂ) (n : ℕ) :
    Differentiable ℂ (fun c : ℂ => (quadratic_map c)^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (fun c : ℂ => (quadratic_map c)^[n + 1] z)
          = (fun c : ℂ => ((quadratic_map c)^[n] z) ^ 2 + c) := by
        funext c; rw [Function.iterate_succ_apply']; rfl
      rw [hstep]; exact (ih.pow 2).add differentiable_id

/-- Standalone additive majorant term bound:
`‖nearOneLogCorrection c n z‖ ≤ (3/2)‖c‖(1/2)^{n+1}` on a large exterior region.
This is the term estimate embedded in
`LogCorrectionSeriesMajorizedOnExterior.of_large_radius`, extracted so it can be
made uniform over a parameter ball. -/
lemma norm_nearOneLogCorrection_le (c : ℂ) (n : ℕ) {R : ℝ}
    (hR : ‖c‖ + 2 ≤ R) {z : ℂ} (hz : R < ‖z‖) :
    ‖nearOneLogCorrection c n z‖ ≤ (3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1) := by
  have hz_ge_c2 : ‖c‖ + 2 ≤ ‖z‖ := le_trans hR (le_of_lt hz)
  have hz_ne : z ≠ 0 := by
    have hpos : 0 < ‖z‖ := by have := norm_nonneg c; linarith
    exact (norm_ne_zero_iff).1 (ne_of_gt hpos)
  have hiter_ge_start : ‖z‖ ≤ ‖(quadratic_map c)^[n] z‖ := by
    have hstart : ‖c‖ + 1 ≤ ‖z‖ := by linarith
    exact iterate_quadratic_map_norm_ge c z n hstart
  have hiter_ge_c2 : ‖c‖ + 2 ≤ ‖(quadratic_map c)^[n] z‖ := le_trans hz_ge_c2 hiter_ge_start
  have hA_ne : (quadratic_map c)^[n] z ≠ 0 := by
    have hpos : 0 < ‖(quadratic_map c)^[n] z‖ := by have := norm_nonneg c; linarith
    exact (norm_ne_zero_iff).1 (ne_of_gt hpos)
  set w : ℂ := c / (((quadratic_map c)^[n] z) ^ 2) with hwdef
  have hw_norm_le_c : ‖w‖ ≤ ‖c‖ := by
    have hden_norm_ge_one : 1 ≤ ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by
      have hbase : 1 ≤ ‖(quadratic_map c)^[n] z‖ := by have := norm_nonneg c; linarith
      calc 1 ≤ ‖(quadratic_map c)^[n] z‖ ^ 2 := by nlinarith
        _ = ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [norm_pow]
    calc ‖w‖ = ‖c‖ / ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [hwdef]
      _ ≤ ‖c‖ := div_le_self (norm_nonneg c) (by linarith)
  have hw_half : ‖w‖ ≤ (1 / 2 : ℝ) := by
    by_cases hc0 : ‖c‖ = 0
    · have : ‖w‖ = 0 := le_antisymm (by simpa [hc0] using hw_norm_le_c) (norm_nonneg _)
      nlinarith
    · have hc_pos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
      have hden_norm_ge : 2 * ‖c‖ ≤ ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by
        calc 2 * ‖c‖ ≤ ‖(quadratic_map c)^[n] z‖ ^ 2 := by nlinarith [norm_nonneg c, hiter_ge_c2]
          _ = ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [norm_pow]
      have hden_pos : 0 < ‖(((quadratic_map c)^[n] z) ^ 2)‖ :=
        lt_of_lt_of_le (by nlinarith : 0 < 2 * ‖c‖) hden_norm_ge
      have hw_eq : ‖w‖ = ‖c‖ / ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [hwdef]
      rw [hw_eq, div_le_iff₀ hden_pos]; nlinarith
  have hlog_bound : ‖Complex.log ((1 : ℂ) + w)‖ ≤ ((3 : ℝ) / 2) * ‖w‖ :=
    Complex.norm_log_one_add_half_le_self hw_half
  have hsimple := nearOneLogCorrection_eq_simple c n z hz_ne hA_ne
  have hscalar_norm : ‖(((2 : ℂ) ^ (n + 1))⁻¹)‖ = (1 / 2 : ℝ) ^ (n + 1) := by
    simp [norm_inv, norm_pow]
  calc ‖nearOneLogCorrection c n z‖
      = ‖(((2 : ℂ) ^ (n + 1))⁻¹) * Complex.log ((1 : ℂ) + w)‖ := by
        rw [hsimple]
    _ = ((1 / 2 : ℝ) ^ (n + 1)) * ‖Complex.log ((1 : ℂ) + w)‖ := by
        rw [norm_mul, hscalar_norm]
    _ ≤ ((1 / 2 : ℝ) ^ (n + 1)) * (((3 : ℝ) / 2) * ‖w‖) :=
        mul_le_mul_of_nonneg_left hlog_bound (pow_nonneg (by norm_num) _)
    _ ≤ ((1 / 2 : ℝ) ^ (n + 1)) * (((3 : ℝ) / 2) * ‖c‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hw_norm_le_c (by norm_num)) (pow_nonneg (by norm_num) _)
    _ = (3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1) := by ring

/-- For a base parameter `c₀` and radius `r > 0`, and a fixed exterior point `z`
with `‖z‖ > ‖c₀‖ + r + 2`, each term `c ↦ nearOneLogCorrection c n z` is
holomorphic on the parameter ball `ball c₀ r`. -/
lemma nearOneLogCorrection_differentiableOn_param
    (c₀ : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ} (n : ℕ)
    (hz : ‖c₀‖ + r + 2 < ‖z‖) :
    DifferentiableOn ℂ (fun c => nearOneLogCorrection c n z) (ball c₀ r) := by
  have hz_ne : z ≠ 0 := by
    have : 0 < ‖z‖ := by have := norm_nonneg c₀; linarith
    exact (norm_ne_zero_iff).1 (ne_of_gt this)
  have hiter : Differentiable ℂ (fun c : ℂ => (quadratic_map c)^[n] z) :=
    differentiable_iterate_param z n
  have hsq : Differentiable ℂ (fun c : ℂ => ((quadratic_map c)^[n] z) ^ 2) := hiter.pow 2
  have hcnorm : ∀ c ∈ ball c₀ r, ‖c‖ < ‖c₀‖ + r := by
    intro c hc
    have h2 : ‖c - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hc)
    calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
      _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
      _ < r + ‖c₀‖ := by linarith
      _ = ‖c₀‖ + r := by ring
  have hden_ne : ∀ c ∈ ball c₀ r, ((quadratic_map c)^[n] z) ^ 2 ≠ 0 := by
    intro c hc
    have hzc : ‖c‖ + 2 < ‖z‖ := by have := hcnorm c hc; linarith
    have hge : ‖z‖ ≤ ‖(quadratic_map c)^[n] z‖ := by
      have hstart : ‖c‖ + 1 ≤ ‖z‖ := by linarith
      exact iterate_quadratic_map_norm_ge c z n hstart
    have hpos : 0 < ‖(quadratic_map c)^[n] z‖ := by have := norm_nonneg c; linarith
    exact pow_ne_zero 2 ((norm_ne_zero_iff).1 (ne_of_gt hpos))
  have hslit : ∀ c ∈ ball c₀ r,
      (1 : ℂ) + c / (((quadratic_map c)^[n] z) ^ 2) ∈ Complex.slitPlane := by
    intro c hc
    have hzc : ‖c‖ + 2 < ‖z‖ := by have := hcnorm c hc; linarith
    exact nearOneLogCorrection_simple_arg_mem_slitPlane_of_large_radius c n (le_refl (‖c‖ + 2)) hzc
  have harg_diff : DifferentiableOn ℂ
      (fun c => (1 : ℂ) + c / (((quadratic_map c)^[n] z) ^ 2)) (ball c₀ r) := by
    have hinv : DifferentiableOn ℂ (fun c => (((quadratic_map c)^[n] z) ^ 2)⁻¹) (ball c₀ r) :=
      (hsq.differentiableOn).inv hden_ne
    have : DifferentiableOn ℂ (fun c => c * (((quadratic_map c)^[n] z) ^ 2)⁻¹) (ball c₀ r) :=
      differentiableOn_id.mul hinv
    simpa [div_eq_mul_inv] using this.const_add (1 : ℂ)
  have hlog_diff : DifferentiableOn ℂ
      (fun c => Complex.log ((1 : ℂ) + c / (((quadratic_map c)^[n] z) ^ 2))) (ball c₀ r) :=
    harg_diff.clog hslit
  have hfinal : DifferentiableOn ℂ
      (fun c => ((2 : ℂ) ^ (n + 1))⁻¹ *
        Complex.log ((1 : ℂ) + c / (((quadratic_map c)^[n] z) ^ 2))) (ball c₀ r) :=
    hlog_diff.const_mul _
  refine hfinal.congr ?_
  intro c hc
  have hA_ne : (quadratic_map c)^[n] z ≠ 0 := by
    have := hden_ne c hc
    exact fun h => this (by rw [h]; ring)
  exact (nearOneLogCorrection_eq_simple c n z hz_ne hA_ne)

/-- **Parameter-holomorphy of the logarithmic correction series.** For a fixed
exterior point `z` with `‖z‖ > ‖c₀‖ + r + 2`, the series `c ↦ logCorrectionSeries c z`
is holomorphic on the parameter ball, via the Weierstrass `M`-test with the
`c`-uniform majorant `(3/2)(‖c₀‖ + r)(1/2)^{n+1}`. -/
lemma logCorrectionSeries_differentiableOn_param
    (c₀ : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖c₀‖ + r + 2 < ‖z‖) :
    DifferentiableOn ℂ (fun c => logCorrectionSeries c z) (ball c₀ r) := by
  have hsum : Summable (fun n : ℕ => (3 / 2 : ℝ) * (‖c₀‖ + r) * (1 / 2 : ℝ) ^ (n + 1)) := by
    have hgeom : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) :=
      summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hshift : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 1))) := by
      simpa [pow_succ'] using (hgeom.mul_left (1 / 2 : ℝ))
    exact hshift.mul_left ((3 / 2 : ℝ) * (‖c₀‖ + r))
  have hbound : ∀ (n : ℕ) (c : ℂ), c ∈ ball c₀ r →
      ‖nearOneLogCorrection c n z‖ ≤ (3 / 2 : ℝ) * (‖c₀‖ + r) * (1 / 2 : ℝ) ^ (n + 1) := by
    intro n c hc
    have hcnorm : ‖c‖ < ‖c₀‖ + r := by
      have h2 : ‖c - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hc)
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < r + ‖c₀‖ := by linarith
        _ = ‖c₀‖ + r := by ring
    have hzc : ‖c‖ + 2 < ‖z‖ := by linarith
    have hterm := norm_nearOneLogCorrection_le c n (le_refl (‖c‖ + 2)) hzc
    have hmul : (3 / 2 : ℝ) * ‖c‖ * (1 / 2 : ℝ) ^ (n + 1)
        ≤ (3 / 2 : ℝ) * (‖c₀‖ + r) * (1 / 2 : ℝ) ^ (n + 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
      exact mul_le_mul_of_nonneg_left (le_of_lt hcnorm) (by norm_num)
    exact le_trans hterm hmul
  have := differentiableOn_tsum_of_summable_norm
    (F := fun n c => nearOneLogCorrection c n z)
    (U := ball c₀ r) hsum
    (fun n => nearOneLogCorrection_differentiableOn_param c₀ hr n hz)
    isOpen_ball hbound
  simpa [logCorrectionSeries] using this

/-- **Parameter-holomorphy of the logarithmic-series Böttcher coordinate.** For a
fixed exterior point `z` with `‖z‖ > ‖c₀‖ + r + 2`, the coordinate
`c ↦ logSeriesBottcherApprox c z` is holomorphic on the parameter ball.  This is
the missing `param_holo` field of the near-infinity genuine Böttcher family. -/
lemma logSeriesBottcherApprox_differentiableOn_param
    (c₀ : ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖c₀‖ + r + 2 < ‖z‖) :
    DifferentiableOn ℂ (fun c => logSeriesBottcherApprox c z) (ball c₀ r) := by
  have hexp : DifferentiableOn ℂ (fun c => Complex.exp (logCorrectionSeries c z)) (ball c₀ r) :=
    (logCorrectionSeries_differentiableOn_param c₀ hr hz).cexp
  have := hexp.const_mul z
  simpa [logSeriesBottcherApprox, logSeriesBottcherRatio] using this


-- Joint continuity in (c, z) of the near-infinity Böttcher family
lemma continuous_iterate_joint (n : ℕ) :
    Continuous (fun p : ℂ × ℂ => (quadratic_map p.1)^[n] p.2) := by
  induction n with
  | zero => simpa using continuous_snd
  | succ n ih =>
      have hstep : (fun p : ℂ × ℂ => (quadratic_map p.1)^[n+1] p.2)
          = (fun p : ℂ × ℂ => ((quadratic_map p.1)^[n] p.2) ^ 2 + p.1) := by
        funext p; rw [Function.iterate_succ_apply']; rfl
      rw [hstep]; exact (ih.pow 2).add continuous_fst

-- per-term joint continuity on product set
lemma nearOneLogCorrection_continuousOn_joint
    (c₀ : ℂ) {r : ℝ} (n : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2)
      (ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖}) := by
  set S := ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖} with hS
  have hiter : Continuous (fun p : ℂ × ℂ => (quadratic_map p.1)^[n] p.2) :=
    continuous_iterate_joint n
  have hcnorm : ∀ p ∈ S, ‖p.1‖ < ‖c₀‖ + r := by
    intro p hp
    have hp1 : p.1 ∈ ball c₀ r := hp.1
    have h2 : ‖p.1 - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hp1)
    calc ‖p.1‖ = ‖(p.1 - c₀) + c₀‖ := by ring_nf
      _ ≤ ‖p.1 - c₀‖ + ‖c₀‖ := norm_add_le _ _
      _ < r + ‖c₀‖ := by linarith
      _ = ‖c₀‖ + r := by ring
  have hzc : ∀ p ∈ S, ‖p.1‖ + 2 < ‖p.2‖ := by
    intro p hp
    have hz2 : ‖c₀‖ + r + 2 < ‖p.2‖ := hp.2
    have := hcnorm p hp; linarith
  have hden_ne : ∀ p ∈ S, ((quadratic_map p.1)^[n] p.2) ^ 2 ≠ 0 := by
    intro p hp
    have hzc' := hzc p hp
    have hge : ‖p.2‖ ≤ ‖(quadratic_map p.1)^[n] p.2‖ := by
      have hstart : ‖p.1‖ + 1 ≤ ‖p.2‖ := by linarith
      exact iterate_quadratic_map_norm_ge p.1 p.2 n hstart
    have hpos : 0 < ‖(quadratic_map p.1)^[n] p.2‖ := by have := norm_nonneg p.1; linarith
    exact pow_ne_zero 2 ((norm_ne_zero_iff).1 (ne_of_gt hpos))
  have hslit : ∀ p ∈ S,
      (1 : ℂ) + p.1 / (((quadratic_map p.1)^[n] p.2) ^ 2) ∈ Complex.slitPlane := by
    intro p hp
    exact nearOneLogCorrection_simple_arg_mem_slitPlane_of_large_radius p.1 n
      (le_refl (‖p.1‖ + 2)) (hzc p hp)
  -- continuity of the simple form
  have harg : ContinuousOn
      (fun p : ℂ × ℂ => (1 : ℂ) + p.1 / (((quadratic_map p.1)^[n] p.2) ^ 2)) S := by
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.div continuousOn_fst
      ((hiter.pow 2).continuousOn) hden_ne
  have hlog : ContinuousOn
      (fun p : ℂ × ℂ => Complex.log ((1 : ℂ) + p.1 / (((quadratic_map p.1)^[n] p.2) ^ 2))) S := by
    apply ContinuousOn.clog harg hslit
  have hfinal : ContinuousOn
      (fun p : ℂ × ℂ => ((2 : ℂ) ^ (n + 1))⁻¹ *
        Complex.log ((1 : ℂ) + p.1 / (((quadratic_map p.1)^[n] p.2) ^ 2))) S :=
    continuousOn_const.mul hlog
  refine hfinal.congr ?_
  intro p hp
  have hz_ne : p.2 ≠ 0 := by
    have : (0:ℝ) < ‖p.2‖ := by have := hzc p hp; have := norm_nonneg p.1; linarith
    exact (norm_ne_zero_iff).1 (ne_of_gt this)
  have hA_ne : (quadratic_map p.1)^[n] p.2 ≠ 0 := by
    have := hden_ne p hp; exact fun h => this (by rw [h]; ring)
  exact (nearOneLogCorrection_eq_simple p.1 n p.2 hz_ne hA_ne)

end MLC

namespace MLC
open Quadratic Complex Topology Set Filter Metric

lemma logCorrectionSeries_continuousOn_joint (c₀ : ℂ) {r : ℝ} (_hr : 0 < r) :
    ContinuousOn (fun p : ℂ × ℂ => logCorrectionSeries p.1 p.2)
      (ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖}) := by
  have hsum : Summable (fun n : ℕ => (3 / 2 : ℝ) * (‖c₀‖ + r) * (1 / 2 : ℝ) ^ (n + 1)) := by
    have hgeom : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) :=
      summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hshift : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 1))) := by
      simpa [pow_succ'] using (hgeom.mul_left (1 / 2 : ℝ))
    exact hshift.mul_left ((3 / 2 : ℝ) * (‖c₀‖ + r))
  have hbound : ∀ (n : ℕ) (p : ℂ × ℂ),
      p ∈ ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖} →
      ‖nearOneLogCorrection p.1 n p.2‖ ≤ (3 / 2 : ℝ) * (‖c₀‖ + r) * (1 / 2 : ℝ) ^ (n + 1) := by
    intro n p hp
    have hcnorm : ‖p.1‖ < ‖c₀‖ + r := by
      have h2 : ‖p.1 - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hp.1)
      calc ‖p.1‖ = ‖(p.1 - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖p.1 - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < r + ‖c₀‖ := by linarith
        _ = ‖c₀‖ + r := by ring
    have hzc : ‖p.1‖ + 2 < ‖p.2‖ := by
      have h2 : ‖c₀‖ + r + 2 < ‖p.2‖ := hp.2
      linarith
    have hterm := norm_nearOneLogCorrection_le p.1 n (le_refl (‖p.1‖ + 2)) hzc
    have hmul : (3 / 2 : ℝ) * ‖p.1‖ * (1 / 2 : ℝ) ^ (n + 1)
        ≤ (3 / 2 : ℝ) * (‖c₀‖ + r) * (1 / 2 : ℝ) ^ (n + 1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
      exact mul_le_mul_of_nonneg_left (le_of_lt hcnorm) (by norm_num)
    exact le_trans hterm hmul
  have hgoal : ContinuousOn (fun p : ℂ × ℂ => ∑' n : ℕ, nearOneLogCorrection p.1 n p.2)
      (ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖}) :=
    continuousOn_tsum (fun n => nearOneLogCorrection_continuousOn_joint c₀ n) hsum hbound
  exact hgoal

lemma logSeriesBottcherApprox_continuousOn_joint (c₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2)
      (ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖}) := by
  have hexp : ContinuousOn (fun p : ℂ × ℂ => Complex.exp (logCorrectionSeries p.1 p.2))
      (ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖}) :=
    Complex.continuous_exp.comp_continuousOn (logCorrectionSeries_continuousOn_joint c₀ hr)
  have hz : ContinuousOn (fun p : ℂ × ℂ => p.2) (ball c₀ r ×ˢ {z : ℂ | ‖c₀‖ + r + 2 < ‖z‖}) :=
    continuousOn_snd
  have hmul := hz.mul hexp
  have heq : (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2)
      = (fun p : ℂ × ℂ => p.2 * Complex.exp (logCorrectionSeries p.1 p.2)) := rfl
  rw [heq]; exact hmul


namespace Quadratic

/-- **First genuine near-infinity Böttcher parameter family.** All five fields are
now discharged with the concrete coordinate `logSeriesBottcherApprox`, on the
exterior region `{‖z‖ > ‖c₀‖ + r + 2}` over the parameter ball `ball c₀ r`.
This replaces the previous forgetful/placeholder constructions with a genuine
holomorphic family, holomorphic in **both** the space variable `z` and the
parameter `c`. -/
noncomputable def logSeriesNearInfinityParameterFamily
    (c₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    GenuineBottcherNearInfinityParameterFamilyData c₀ where
  r := r
  R := ‖c₀‖ + r + 2
  r_pos := hr
  R_pos := by have := norm_nonneg c₀; linarith
  phi := fun c z => MLC.logSeriesBottcherApprox c z
  norm_on_exterior := by
    intro c hc z hz
    have hcnorm : ‖c‖ < ‖c₀‖ + r := by
      have h2 : ‖c - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hc)
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < r + ‖c₀‖ := by linarith
        _ = ‖c₀‖ + r := by ring
    have hzc : ‖z‖ > ‖c‖ + 2 := by
      have : (‖c₀‖ + r + 2 : ℝ) < ‖z‖ := hz
      linarith
    exact MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hzc
  conj_on_exterior := by
    intro c hc z hz
    have hcnorm : ‖c‖ < ‖c₀‖ + r := by
      have h2 : ‖c - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hc)
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < r + ‖c₀‖ := by linarith
        _ = ‖c₀‖ + r := by ring
    have hR : ‖c‖ + 2 ≤ ‖c₀‖ + r + 2 := by linarith
    exact MLC.logSeriesBottcherApprox_conj_of_large_radius c hR hz
  fiber_holo_on_exterior := by
    intro c hc
    have hcnorm : ‖c‖ < ‖c₀‖ + r := by
      have h2 : ‖c - c₀‖ < r := by simpa [dist_eq_norm] using (mem_ball.1 hc)
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ < r + ‖c₀‖ := by linarith
        _ = ‖c₀‖ + r := by ring
    have hR : ‖c‖ + 2 ≤ ‖c₀‖ + r + 2 := by linarith
    exact MLC.logSeriesBottcherApprox_differentiableOn_large_radius c hR
  tendsto_div_atInfinity := by
    intro c _
    exact MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c
  param_holo_on_exterior := by
    intro z hz
    exact MLC.logSeriesBottcherApprox_differentiableOn_param c₀ hr hz

end Quadratic

end MLC
