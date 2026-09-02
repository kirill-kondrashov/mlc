import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinCoordinate
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Analytic

/-!
# The Green function is harmonic on the basin of infinity

This file discharges **Linchpin 1** of the Route-A potential-theory proof of
sub-level connectivity: the Green function `green_function c` is harmonic on the
basin of infinity `basin_of_infinity c`.

The proof avoids any "harmonic under locally-uniform limits" theorem (a Mathlib
gap).  Instead it uses the genuine analytic near-infinity Böttcher coordinate
`logSeriesBottcherApprox c =: φ` already built in the repository:

* On the canonical outside-open region `{‖z‖ > ‖c‖ + 2}` we prove the identity
  `green_function c z = Real.log ‖φ z‖` (Böttcher uniqueness via the shared
  functional equation and the `→ 0` normalisation at infinity).
* For a general basin point `p`, choosing an escape time `N` with
  `‖fᴺ p‖ > ‖c‖ + 2`, the Green functional equation gives locally
  `green_function c z = (2ᴺ)⁻¹ · log ‖φ (fᴺ z)‖`, whose right-hand side is
  harmonic by `AnalyticAt.harmonicAt_log_norm` applied to the analytic
  nonvanishing function `φ ∘ fᴺ`.
-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric Real InnerProductSpace

namespace Quadratic

/-- The logarithmic-series Böttcher coordinate is nonzero away from `0`: it is
`z · exp (logCorrectionSeries c z)`, and the exponential never vanishes. -/
lemma logSeriesBottcherApprox_ne_zero (c : ℂ) {u : ℂ} (hu : u ≠ 0) :
    MLC.logSeriesBottcherApprox c u ≠ 0 := by
  have : MLC.logSeriesBottcherApprox c u
      = u * Complex.exp (MLC.logCorrectionSeries c u) := rfl
  rw [this]
  exact mul_ne_zero hu (Complex.exp_ne_zero _)

/-- **Böttcher uniqueness on the outside-open region.**  There the Green
function equals `log ‖φ‖` for the logarithmic-series coordinate `φ`. -/
lemma green_function_eq_log_norm_logSeries_of_outside_open
    (c : ℂ) {z : ℂ} (hz : ‖z‖ > ‖c‖ + 2) :
    green_function c z = Real.log ‖MLC.logSeriesBottcherApprox c z‖ := by
  set φ := MLC.logSeriesBottcherApprox c with hφdef
  set w : ℕ → ℂ := fun n => (MLC.quadratic_map c)^[n] z with hwdef
  -- log ‖φ (fⁿ z)‖ = 2ⁿ · log ‖φ z‖
  have hconj : ∀ n, Real.log ‖φ (w n)‖ = (2 : ℝ) ^ n * Real.log ‖φ z‖ := by
    intro n
    have h := MLC.logSeriesBottcherApprox_conj_iterate_outside_open c hz n
    have h' : φ (w n) = (φ z) ^ (2 ^ n) := h
    rw [h', norm_pow, Real.log_pow]
    push_cast; ring
  -- green (fⁿ z) = 2ⁿ · green z
  have hgreen : ∀ n, green_function c (w n) = (2 : ℝ) ^ n * green_function c z := by
    intro n
    simpa [hwdef] using green_function_orbit_eq_local c z n
  -- both correction terms vanish at infinity
  have hQ : Tendsto (fun u => green_function c u - Real.log ‖u‖) atInfinity (𝓝 0) :=
    MLC.tendsto_green_function_minus_log_norm_atInfinity c
  have hP : Tendsto (fun u => Real.log ‖φ u‖ - Real.log ‖u‖) atInfinity (𝓝 0) := by
    have hdiv : Tendsto (fun u => φ u / u) atInfinity (𝓝 1) :=
      MLC.tendsto_logSeriesBottcherApprox_div_atInfinity c
    have hlog : Tendsto (fun u => Real.log ‖φ u / u‖) atInfinity (𝓝 0) := by
      have hca : ContinuousAt (fun w : ℂ => Real.log ‖w‖) (1 : ℂ) :=
        (Real.continuousAt_log (by simp)).comp continuous_norm.continuousAt
      have h : Tendsto (fun u => Real.log ‖φ u / u‖) atInfinity (𝓝 (Real.log ‖(1 : ℂ)‖)) :=
        hca.tendsto.comp hdiv
      simpa using h
    have hune : ∀ᶠ u in atInfinity, u ≠ 0 := by
      filter_upwards [MLC.eventually_atInfinity_norm_gt 0] with u hu
      exact norm_pos_iff.1 hu
    refine (Filter.tendsto_congr' ?_).2 hlog
    filter_upwards [hune] with u hu
    have hφu : φ u ≠ 0 := logSeriesBottcherApprox_ne_zero c hu
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hφu) (norm_ne_zero_iff.2 hu)]
  -- w n → ∞
  have hwInf : Tendsto w atTop atInfinity := by
    have hcomp : Tendsto (fun n => ‖w n‖) atTop atTop := by
      simpa [hwdef] using iterate_quadratic_map_tendsto_infty c z (le_of_lt hz)
    exact Filter.tendsto_comap_iff.2 hcomp
  -- Bₙ := log ‖φ (wₙ)‖ - green (wₙ) → 0
  have hBP : Tendsto (fun n => Real.log ‖φ (w n)‖ - Real.log ‖w n‖) atTop (𝓝 0) :=
    hP.comp hwInf
  have hBQ : Tendsto (fun n => green_function c (w n) - Real.log ‖w n‖) atTop (𝓝 0) :=
    hQ.comp hwInf
  have hB : Tendsto (fun n => Real.log ‖φ (w n)‖ - green_function c (w n)) atTop (𝓝 0) := by
    have heq : (fun n => Real.log ‖φ (w n)‖ - green_function c (w n))
        = (fun n => (Real.log ‖φ (w n)‖ - Real.log ‖w n‖)
            - (green_function c (w n) - Real.log ‖w n‖)) := by
      funext n; ring
    rw [heq]; simpa using hBP.sub hBQ
  -- Bₙ = 2ⁿ · (log ‖φ z‖ - green z)
  have hBform : ∀ n, Real.log ‖φ (w n)‖ - green_function c (w n)
      = (2 : ℝ) ^ n * (Real.log ‖φ z‖ - green_function c z) := by
    intro n; rw [hconj n, hgreen n]; ring
  -- (2ⁿ)⁻¹ · Bₙ = (log ‖φ z‖ - green z), a constant sequence, which tends to 0
  have hinv : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    have : (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) = (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) := by
      funext n; rw [inv_pow]
    rw [this]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hconst : Tendsto (fun _ : ℕ => Real.log ‖φ z‖ - green_function c z) atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun n => ((2 : ℝ) ^ n)⁻¹ * (Real.log ‖φ (w n)‖ - green_function c (w n)))
        atTop (𝓝 0) := by
      simpa using hinv.mul hB
    have hEq : (fun n => ((2 : ℝ) ^ n)⁻¹ * (Real.log ‖φ (w n)‖ - green_function c (w n)))
        = (fun _ : ℕ => Real.log ‖φ z‖ - green_function c z) := by
      funext n
      rw [hBform n]
      have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
      rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    rwa [hEq] at hmul
  have hzero : Real.log ‖φ z‖ - green_function c z = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  linarith [hzero]

/-- **Linchpin 1 (pointwise).**  The Green function is harmonic at every point of
the basin of infinity. -/
theorem green_function_harmonicAt_of_mem_basin
    (c : ℂ) {p : ℂ} (hp : p ∈ basin_of_infinity c) :
    HarmonicAt (green_function c) p := by
  set N := basinEscapeTime c p hp with hN
  set φ := MLC.logSeriesBottcherApprox c with hφdef
  have hwout : ‖(MLC.quadratic_map c)^[N] p‖ > ‖c‖ + 2 := basinEscapeTime_spec c p hp
  -- the analytic nonvanishing function g = φ ∘ fᴺ
  set g : ℂ → ℂ := fun z => φ ((MLC.quadratic_map c)^[N] z) with hgdef
  have hiter_analytic : AnalyticAt ℂ ((MLC.quadratic_map c)^[N]) p := by
    have hdiff : DifferentiableOn ℂ ((MLC.quadratic_map c)^[N]) univ :=
      ((quadratic_map_differentiable c).iterate N).differentiableOn
    exact hdiff.analyticAt univ_mem
  have hOpen : IsOpen {z : ℂ | ‖c‖ + 2 < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm
  have hφ_analytic : AnalyticAt ℂ φ ((MLC.quadratic_map c)^[N] p) := by
    have hdiff : DifferentiableOn ℂ φ {z : ℂ | ‖c‖ + 2 < ‖z‖} :=
      MLC.logSeriesBottcherApprox_differentiableOn_large_radius c (le_refl _)
    exact hdiff.analyticAt (hOpen.mem_nhds hwout)
  have hg_analytic : AnalyticAt ℂ g p := hφ_analytic.comp hiter_analytic
  have hg_ne : g p ≠ 0 :=
    logSeriesBottcherApprox_ne_zero c (by
      exact norm_pos_iff.1 (lt_trans (by positivity) hwout))
  have hharm_log : HarmonicAt (fun z => Real.log ‖g z‖) p :=
    hg_analytic.harmonicAt_log_norm hg_ne
  have hharm_smul : HarmonicAt (((2 : ℝ) ^ N)⁻¹ • fun z => Real.log ‖g z‖) p :=
    hharm_log.const_smul
  -- green equals `(2ᴺ)⁻¹ • log ‖g‖` on a neighbourhood of `p`
  have hnhds : {z : ℂ | ‖c‖ + 2 < ‖(MLC.quadratic_map c)^[N] z‖} ∈ 𝓝 p := by
    have hcont : Continuous fun z : ℂ => (MLC.quadratic_map c)^[N] z :=
      (quadratic_map_differentiable c).continuous.iterate N
    have : IsOpen {z : ℂ | ‖c‖ + 2 < ‖(MLC.quadratic_map c)^[N] z‖} :=
      hOpen.preimage hcont
    exact this.mem_nhds hwout
  have hEq : green_function c
      =ᶠ[𝓝 p] (((2 : ℝ) ^ N)⁻¹ • fun z => Real.log ‖g z‖) := by
    filter_upwards [hnhds] with z hz
    have hzout : ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2 := hz
    have hgreenN : green_function c ((MLC.quadratic_map c)^[N] z)
        = (2 : ℝ) ^ N * green_function c z := green_function_orbit_eq_local c z N
    have hidentity : green_function c ((MLC.quadratic_map c)^[N] z)
        = Real.log ‖φ ((MLC.quadratic_map c)^[N] z)‖ :=
      green_function_eq_log_norm_logSeries_of_outside_open c hzout
    have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    simp only [Pi.smul_apply, smul_eq_mul, hgdef]
    rw [hidentity] at hgreenN
    rw [hgreenN, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  exact (harmonicAt_congr_nhds hEq).2 hharm_smul

end Quadratic

end MLC
