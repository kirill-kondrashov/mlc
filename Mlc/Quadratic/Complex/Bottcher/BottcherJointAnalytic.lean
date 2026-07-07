import Mlc.Quadratic.Complex.Bottcher.BottcherInverse

/-!
# Joint (two-variable) analyticity of the logarithmic-series Böttcher terms

This file establishes **joint** analyticity in `(c, z)` of the individual
Böttcher correction terms `nearOneLogCorrection c n z` and of the finite
approximants built from them (`finiteLogCorrectionSum`,
`finiteLogSeriesBottcherApprox`).

Unlike separate holomorphy in `c` (`BottcherParamHolo.lean`) or in `z`
(`BottcherOutsidePlan.lean`), joint `ℂ²`-analyticity does **not** follow from a
Weierstrass/M-test argument in Mathlib — there is no several-complex-variables
analyticity-of-limits theorem (no Osgood/Hartogs). We instead exploit that each
term is a **finite composition of analytic combinators**: the iterate
`(quadratic_map c)^[n] z` is a polynomial in `(c, z)`, and the term is
`(2^(n+1))⁻¹ · log(1 + c/(f_c^n z)²)`, analytic wherever the iterate is nonzero
and the log-argument lies in the slit plane — both automatic on the exterior
`‖c‖ + 2 < ‖z‖`.

This reduces the still-open joint analyticity of the *full* Böttcher coordinate
`logSeriesBottcherApprox` (and hence the parametrized holomorphic inverse) to the
single missing keystone: a joint M-test analyticity of the `tsum` over a `ℂ²`
domain.
-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric

/-- The iterate `(quadratic_map c)^[n] z` is jointly analytic in `(c, z)`:
each step `w ↦ w² + c` is a polynomial in both variables. -/
lemma analyticAt_iterate_joint (n : ℕ) (x : ℂ × ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => (quadratic_map p.1)^[n] p.2) x := by
  induction n with
  | zero => simpa using (analyticAt_snd (𝕜 := ℂ) (p := x))
  | succ n ih =>
      have hstep : (fun p : ℂ × ℂ => (quadratic_map p.1)^[n + 1] p.2)
          = fun p : ℂ × ℂ => ((quadratic_map p.1)^[n] p.2) ^ 2 + p.1 := by
        funext p; rw [Function.iterate_succ_apply']; rfl
      rw [hstep]
      exact (ih.pow 2).add analyticAt_fst

/-- Joint analyticity of the *simple form* of the correction term
`(2^(n+1))⁻¹·log(1 + c/(f_c^n z)²)` at a base point where the iterate is
nonzero and the log-argument lies in the slit plane. -/
lemma analyticAt_nearOneLogCorrectionSimple_joint (n : ℕ) {x : ℂ × ℂ}
    (hA : (quadratic_map x.1)^[n] x.2 ≠ 0)
    (harg : (1 : ℂ) + x.1 / ((quadratic_map x.1)^[n] x.2) ^ 2 ∈ slitPlane) :
    AnalyticAt ℂ
      (fun p : ℂ × ℂ => ((2 : ℂ) ^ (n + 1))⁻¹ *
        Complex.log ((1 : ℂ) + p.1 / ((quadratic_map p.1)^[n] p.2) ^ 2)) x := by
  have hIter := analyticAt_iterate_joint n x
  have hAsq : AnalyticAt ℂ (fun p : ℂ × ℂ => ((quadratic_map p.1)^[n] p.2) ^ 2) x :=
    hIter.pow 2
  have hAsq0 : ((quadratic_map x.1)^[n] x.2) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hInv : AnalyticAt ℂ (fun p : ℂ × ℂ => (((quadratic_map p.1)^[n] p.2) ^ 2)⁻¹) x :=
    hAsq.inv hAsq0
  have hFrac : AnalyticAt ℂ
      (fun p : ℂ × ℂ => p.1 / ((quadratic_map p.1)^[n] p.2) ^ 2) x := by
    have hEq : (fun p : ℂ × ℂ => p.1 / ((quadratic_map p.1)^[n] p.2) ^ 2)
        = fun p : ℂ × ℂ => p.1 * (((quadratic_map p.1)^[n] p.2) ^ 2)⁻¹ := by
      funext p; rw [div_eq_mul_inv]
    rw [hEq]; exact analyticAt_fst.mul hInv
  have hArg : AnalyticAt ℂ
      (fun p : ℂ × ℂ => (1 : ℂ) + p.1 / ((quadratic_map p.1)^[n] p.2) ^ 2) x :=
    analyticAt_const.add hFrac
  exact analyticAt_const.mul (hArg.clog harg)

/-- **Joint analyticity of the Böttcher correction term.**  At a base point
`(c₀, z₀)` with `z₀ ≠ 0`, nonzero iterate, and log-argument in the slit plane,
`(c, z) ↦ nearOneLogCorrection c n z` is jointly analytic in `(c, z)`. -/
lemma analyticAt_nearOneLogCorrection_joint (n : ℕ) {x : ℂ × ℂ}
    (hz : x.2 ≠ 0)
    (hA : (quadratic_map x.1)^[n] x.2 ≠ 0)
    (harg : (1 : ℂ) + x.1 / ((quadratic_map x.1)^[n] x.2) ^ 2 ∈ slitPlane) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) x := by
  have hSimple := analyticAt_nearOneLogCorrectionSimple_joint n hA harg
  have hIterCont : ContinuousAt (fun p : ℂ × ℂ => (quadratic_map p.1)^[n] p.2) x :=
    (analyticAt_iterate_joint n x).continuousAt
  have hSndCont : ContinuousAt (fun p : ℂ × ℂ => p.2) x := continuous_snd.continuousAt
  have hAne : ∀ᶠ p in 𝓝 x, (quadratic_map p.1)^[n] p.2 ≠ 0 :=
    hIterCont.eventually_ne hA
  have hzne : ∀ᶠ p in 𝓝 x, p.2 ≠ 0 := hSndCont.eventually_ne hz
  have hEq : (fun p : ℂ × ℂ => ((2 : ℂ) ^ (n + 1))⁻¹ *
        Complex.log ((1 : ℂ) + p.1 / ((quadratic_map p.1)^[n] p.2) ^ 2))
        =ᶠ[𝓝 x] fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2 := by
    filter_upwards [hAne, hzne] with p hpA hpz
    exact (nearOneLogCorrection_eq_simple p.1 n p.2 hpz hpA).symm
  exact hSimple.congr hEq

/-- **Exterior joint analyticity of the Böttcher correction term.**  On the
exterior `‖c‖ + 2 < ‖z‖` the three hypotheses of
`analyticAt_nearOneLogCorrection_joint` hold automatically, so the term is
jointly analytic at `(c, z)`. -/
lemma analyticAt_nearOneLogCorrection_joint_exterior (n : ℕ) {x : ℂ × ℂ}
    (hx : ‖x.1‖ + 2 < ‖x.2‖) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => nearOneLogCorrection p.1 n p.2) x := by
  obtain ⟨c, z⟩ := x
  simp only at hx ⊢
  have hz0 : z ≠ 0 := by
    have : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt (by positivity) hx
    exact norm_pos_iff.1 this
  have hstart : ‖z‖ ≥ ‖c‖ + 1 := by linarith
  have hIterGe : ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ :=
    iterate_quadratic_map_norm_ge c z n hstart
  have hAgt : ‖c‖ + 2 < ‖(quadratic_map c)^[n] z‖ := lt_of_lt_of_le hx hIterGe
  have hA0 : (quadratic_map c)^[n] z ≠ 0 := by
    have : (0 : ℝ) < ‖(quadratic_map c)^[n] z‖ := lt_of_le_of_lt (by positivity) hAgt
    exact norm_pos_iff.1 this
  set A := (quadratic_map c)^[n] z with hA
  have hApos : 0 < ‖A‖ := lt_of_le_of_lt (by positivity) hAgt
  have hfrac_lt : ‖c / A ^ 2‖ < 1 := by
    rw [norm_div, norm_pow]
    rw [div_lt_one (by positivity)]
    nlinarith [norm_nonneg c, hApos, hAgt]
  have harg : (1 : ℂ) + c / A ^ 2 ∈ slitPlane := by
    left
    have hle : |(c / A ^ 2).re| ≤ ‖c / A ^ 2‖ := Complex.abs_re_le_norm _
    have hge : -‖c / A ^ 2‖ ≤ (c / A ^ 2).re := (abs_le.1 hle).1
    have hpos : 0 < ((1 : ℂ) + c / A ^ 2).re := by
      rw [Complex.add_re, Complex.one_re]; linarith [hfrac_lt]
    exact hpos
  exact analyticAt_nearOneLogCorrection_joint n hz0 hA0 harg

/-- **Joint analyticity of the finite correction sum** on the exterior. -/
lemma analyticAt_finiteLogCorrectionSum_joint_exterior (n : ℕ) {x : ℂ × ℂ}
    (hx : ‖x.1‖ + 2 < ‖x.2‖) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => finiteLogCorrectionSum p.1 n p.2) x := by
  have hEq : (fun p : ℂ × ℂ => finiteLogCorrectionSum p.1 n p.2)
      = fun p : ℂ × ℂ => ∑ k ∈ Finset.range n, nearOneLogCorrection p.1 k p.2 := rfl
  rw [hEq]
  exact Finset.analyticAt_fun_sum _
    (fun k _ => analyticAt_nearOneLogCorrection_joint_exterior k hx)

/-- **Joint analyticity of the finite Böttcher approximant** on the exterior. -/
lemma analyticAt_finiteLogSeriesBottcherApprox_joint_exterior (n : ℕ) {x : ℂ × ℂ}
    (hx : ‖x.1‖ + 2 < ‖x.2‖) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => finiteLogSeriesBottcherApprox p.1 n p.2) x := by
  have hEq : (fun p : ℂ × ℂ => finiteLogSeriesBottcherApprox p.1 n p.2)
      = fun p : ℂ × ℂ => p.2 * Complex.exp (finiteLogCorrectionSum p.1 n p.2) := rfl
  rw [hEq]
  exact analyticAt_snd.mul
    ((analyticAt_finiteLogCorrectionSum_joint_exterior n hx).cexp)

end MLC
