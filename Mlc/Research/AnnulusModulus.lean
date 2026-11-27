import Mlc.Research.ExtremalLength
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The modulus of a round annulus

`Mlc/Research/ExtremalLength.lean` defines the extremal length of a family of curves given by
length measures, for an area measure. This module computes it in the model case that fixes the
normalization of every other estimate, the round annulus `A(r, R) = {r < |z| < R}` of the plane
with Lebesgue measure, in polar coordinates.

* `extLength_radialFamily`: the family of the radial segments `s ↦ s e^{iθ}`, `r < s < R`, which
  join the two boundary circles, has extremal length `log (R / r) / (2π)`;
* `extLength_circleFamily`: the family of the circles `|z| = s`, `r < s < R`, which separate the
  boundary circles, has extremal length `2π / log (R / r)`;
* `extLength_radialFamily_mul_circleFamily`: the two are reciprocal;
* `extLength_radialFamily_add_le`: the series law of `ExtremalLength.lean` for concentric
  annuli, the Grötzsch inequality in the model.

So the abstract definition agrees with the classical modulus `mod A(r, R) = log (R / r) / (2π)`.
The upper bounds are the Cauchy–Schwarz inequality in polar coordinates (`radial_cs`,
`circle_cs`), and the lower bounds are given by the metric `1 / |z|` (`annulusMetric`).
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real

noncomputable section

/-- Cauchy–Schwarz for lower integrals with values in `ℝ≥0∞`. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have key : ∀ x : ℝ≥0∞, (x ^ (1 / (2 : ℝ))) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by rw [mul_pow, key, key]

/-! ### Polar coordinates -/

/-- The point of the plane with polar coordinates `(s, θ)`. -/
def pol (p : ℝ × ℝ) : ℂ := p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I)

lemma polarCoord_symm_eq_pol (p : ℝ × ℝ) : Complex.polarCoord.symm p = pol p :=
  Complex.polarCoord_symm_apply p

lemma continuous_pol : Continuous pol := by
  unfold pol
  fun_prop

lemma measurable_pol : Measurable pol := continuous_pol.measurable

lemma norm_pol {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) : ‖pol (s, θ)‖ = s := by
  have := Complex.norm_polarCoord_symm (s, θ)
  rw [polarCoord_symm_eq_pol, abs_of_nonneg hs] at this
  exact this

/-- The polar-coordinates formula for the lower integral over the plane. -/
lemma lintegral_polar (g : ℂ → ℝ≥0∞) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * g (pol p) = ∫⁻ z, g z := by
  have h := Complex.lintegral_comp_polarCoord_symm g
  rw [polarCoord_target] at h
  simp only [polarCoord_symm_eq_pol, smul_eq_mul] at h
  exact h

/-- Integration over the polar rectangle in the order angle, then radius. -/
lemma lintegral_polar_rectangle (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, F p =
      ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioi (0 : ℝ), F (s, θ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_symm F hF.aemeasurable

/-- Integration over the polar rectangle in the order radius, then angle. -/
lemma lintegral_polar_rectangle' (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, F p =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, F (s, θ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod F hF.aemeasurable

/-! ### The radial family -/

/-- The length measure of the radial segment `s ↦ s e^{iθ}`, `r < s ≤ R`. -/
def radialCurve (r R θ : ℝ) : Measure ℂ :=
  (volume.restrict (Ioc r R)).map fun s : ℝ => pol (s, θ)

/-- The radial segments of the annulus `{r < |z| < R}`: the curves that join its two boundary
circles. -/
def radialFamily (r R : ℝ) : Set (Measure ℂ) := range (radialCurve r R)

lemma measurable_pol_left (θ : ℝ) : Measurable fun s : ℝ => pol (s, θ) :=
  measurable_pol.comp (measurable_id.prodMk measurable_const)

lemma rhoLength_radialCurve {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (r R θ : ℝ) :
    rhoLength ρ (radialCurve r R θ) = ∫⁻ s in Ioc r R, ρ (pol (s, θ)) := by
  unfold rhoLength radialCurve
  exact lintegral_map hρ (measurable_pol_left θ)

/-- The integral of `1 / s` over `(r, R]` is `log (R / r)`. -/
lemma lintegral_inv_Ioc {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∫⁻ s in Ioc r R, ENNReal.ofReal s⁻¹ = ENNReal.ofReal (Real.log (R / r)) := by
  have hint : IntervalIntegrable (fun s : ℝ => s⁻¹) volume r R := by
    refine intervalIntegral.intervalIntegrable_inv (fun x hx => ?_) continuousOn_id
    rw [Set.uIcc_of_le hrR] at hx
    exact (hr.trans_le hx.1).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le hrR, integral_inv_of_pos hr (hr.trans_le hrR)]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hrR).1 hint
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    exact (inv_pos.2 (hr.trans hs.1)).le

/-- Cauchy–Schwarz along a ray: the squared length of a ray is at most `log (R / r)` times its
weighted area. -/
lemma radial_cs {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ s in Ioc r R, g s) ^ 2 ≤
      (∫⁻ s in Ioc r R, ENNReal.ofReal s * g s ^ 2) * ENNReal.ofReal (Real.log (R / r)) := by
  have hsqrt : Measurable fun s : ℝ => ENNReal.ofReal (Real.sqrt s) :=
    ENNReal.measurable_ofReal.comp Real.continuous_sqrt.measurable
  have hinv : Measurable fun s : ℝ => ENNReal.ofReal (1 / Real.sqrt s) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div Real.continuous_sqrt.measurable)
  have h1 : ∀ s ∈ Ioc r R,
      g s = g s * ENNReal.ofReal (Real.sqrt s) * ENNReal.ofReal (1 / Real.sqrt s) := by
    intro s hs
    have hq : 0 < Real.sqrt s := Real.sqrt_pos.2 (hr.trans hs.1)
    rw [mul_assoc, ← ENNReal.ofReal_mul hq.le, mul_one_div_cancel hq.ne', ENNReal.ofReal_one,
      mul_one]
  have h2 : ∀ s ∈ Ioc r R,
      (g s * ENNReal.ofReal (Real.sqrt s)) ^ 2 = ENNReal.ofReal s * g s ^ 2 := by
    intro s hs
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg s), Real.sq_sqrt (hr.trans hs.1).le,
      mul_comm]
  have h3 : ∀ s ∈ Ioc r R, ENNReal.ofReal (1 / Real.sqrt s) ^ 2 = ENNReal.ofReal s⁻¹ := by
    intro s hs
    rw [← ENNReal.ofReal_pow (by positivity), div_pow, Real.sq_sqrt (hr.trans hs.1).le, one_pow,
      one_div]
  calc (∫⁻ s in Ioc r R, g s) ^ 2
      = (∫⁻ s in Ioc r R,
          g s * ENNReal.ofReal (Real.sqrt s) * ENNReal.ofReal (1 / Real.sqrt s)) ^ 2 := by
        rw [setLIntegral_congr_fun measurableSet_Ioc h1]
    _ ≤ (∫⁻ s in Ioc r R, (g s * ENNReal.ofReal (Real.sqrt s)) ^ 2) *
          ∫⁻ s in Ioc r R, ENNReal.ofReal (1 / Real.sqrt s) ^ 2 :=
        lintegral_mul_sq_le _ (hg.mul hsqrt).aemeasurable hinv.aemeasurable
    _ = _ := by
        rw [setLIntegral_congr_fun measurableSet_Ioc h2, setLIntegral_congr_fun measurableSet_Ioc h3,
          lintegral_inv_Ioc hr hrR]

/-- **Upper bound for the radial family.** For every metric, the squared least length of the
radial segments is at most `log (R / r) / (2π)` times the area. -/
theorem ratio_radialFamily_le {r R : ℝ} (hr : 0 < r) (hrR : r < R) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    minLength ρ (radialFamily r R) ^ 2 / rhoArea volume ρ ≤
      ENNReal.ofReal (Real.log (R / r) / (2 * π)) := by
  set L := minLength ρ (radialFamily r R) with hL
  set A := rhoArea volume ρ with hA
  have hθ : ∀ θ : ℝ, L ^ 2 ≤ (∫⁻ s in Ioc r R, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2) *
      ENNReal.ofReal (Real.log (R / r)) := by
    intro θ
    calc L ^ 2 ≤ (∫⁻ s in Ioc r R, ρ (pol (s, θ))) ^ 2 := by
          gcongr
          rw [← rhoLength_radialCurve hρ r R θ]
          exact minLength_le_rhoLength ⟨θ, rfl⟩
      _ ≤ _ := radial_cs hr hrR.le (hρ.comp (measurable_pol_left θ))
  have hF : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ρ (pol p) ^ 2 :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul ((hρ.comp measurable_pol).pow_const 2)
  have hpolar : ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioc r R, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 ≤ A := by
    calc ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioc r R, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2
        ≤ ∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 :=
          lintegral_mono fun θ =>
            lintegral_mono' (Measure.restrict_mono (fun s hs => hr.trans hs.1) le_rfl) le_rfl
      _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * ρ (pol p) ^ 2 :=
          (lintegral_polar_rectangle _ hF).symm
      _ = A := lintegral_polar fun z => ρ z ^ 2
  have hint : ENNReal.ofReal (2 * π) * L ^ 2 ≤ ENNReal.ofReal (Real.log (R / r)) * A := by
    calc ENNReal.ofReal (2 * π) * L ^ 2 = ∫⁻ _ in Ioo (-π) π, L ^ 2 := by
          rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
          congr 2
          ring
      _ ≤ ∫⁻ θ in Ioo (-π) π, (∫⁻ s in Ioc r R, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2) *
            ENNReal.ofReal (Real.log (R / r)) := lintegral_mono hθ
      _ = (∫⁻ θ in Ioo (-π) π, ∫⁻ s in Ioc r R, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2) *
            ENNReal.ofReal (Real.log (R / r)) := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ A * ENNReal.ofReal (Real.log (R / r)) := by gcongr
      _ = _ := mul_comm _ _
  have h2π : ENNReal.ofReal (2 * π) ≠ 0 := by
    simp [Real.pi_pos]
  rcases eq_or_ne A 0 with h0 | h0
  · rw [h0, mul_zero, nonpos_iff_eq_zero] at hint
    have : L ^ 2 = 0 := (mul_eq_zero.1 hint).resolve_left h2π
    rw [this, h0]
    simp
  rcases eq_or_ne A ⊤ with htop | htop
  · rw [htop]
    simp
  rw [ENNReal.div_le_iff h0 htop]
  refine (ENNReal.mul_le_mul_iff_right h2π ENNReal.ofReal_ne_top).1 ?_
  calc ENNReal.ofReal (2 * π) * L ^ 2
      ≤ ENNReal.ofReal (Real.log (R / r)) * A := hint
    _ = ENNReal.ofReal (2 * π) * (ENNReal.ofReal (Real.log (R / r) / (2 * π)) * A) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_div_cancel₀ _ (by positivity)]

/-- The metric `1 / |z|` on the annulus `{r < |z| ≤ R}`. -/
def annulusMetric (r R : ℝ) (z : ℂ) : ℝ≥0∞ :=
  if r < ‖z‖ ∧ ‖z‖ ≤ R then ENNReal.ofReal ‖z‖⁻¹ else 0

lemma measurable_annulusMetric (r R : ℝ) : Measurable (annulusMetric r R) := by
  unfold annulusMetric
  refine Measurable.ite ?_ (ENNReal.measurable_ofReal.comp measurable_norm.inv) measurable_const
  exact (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

lemma annulusMetric_pol {r R s : ℝ} (θ : ℝ) (hs : 0 ≤ s) :
    annulusMetric r R (pol (s, θ)) = (Ioc r R).indicator (fun s => ENNReal.ofReal s⁻¹) s := by
  unfold annulusMetric
  rw [norm_pol hs, Set.indicator_apply]
  simp only [Set.mem_Ioc]

/-- Every radial segment has length `log (R / r)` for the metric `1 / |z|`. -/
lemma rhoLength_annulusMetric {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (θ : ℝ) :
    rhoLength (annulusMetric r R) (radialCurve r R θ) = ENNReal.ofReal (Real.log (R / r)) := by
  rw [rhoLength_radialCurve (measurable_annulusMetric r R), ← lintegral_inv_Ioc hr hrR]
  refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [annulusMetric_pol θ (hr.trans hs.1).le, Set.indicator_of_mem hs]

/-- The metric `1 / |z|` has area `2π log (R / r)`. -/
lemma rhoArea_annulusMetric {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rhoArea volume (annulusMetric r R) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r)) := by
  have hF : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * annulusMetric r R (pol p) ^ 2 :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (((measurable_annulusMetric r R).comp measurable_pol).pow_const 2)
  have hinner : ∀ θ : ℝ, ∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal s * annulusMetric r R (pol (s, θ)) ^ 2 = ENNReal.ofReal (Real.log (R / r)) := by
    intro θ
    have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal s * annulusMetric r R (pol (s, θ)) ^ 2 =
        (Ioc r R).indicator (fun s => ENNReal.ofReal s⁻¹) s := by
      intro s hs
      have hs0 : 0 < s := hs
      rw [annulusMetric_pol θ hs0.le]
      by_cases h : s ∈ Ioc r R
      · rw [Set.indicator_of_mem h, ← ENNReal.ofReal_pow (inv_nonneg.2 hs0.le),
          ← ENNReal.ofReal_mul hs0.le]
        congr 1
        field_simp
      · simp [h]
    have hset : Ioc r R ∩ Ioi (0 : ℝ) = Ioc r R :=
      Set.inter_eq_left.2 fun s hs => (hr.trans hs.1 : 0 < s)
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, hset, lintegral_inv_Ioc hr hrR]
  unfold rhoArea
  rw [← lintegral_polar fun z => annulusMetric r R z ^ 2, lintegral_polar_rectangle _ hF]
  simp only [hinner]
  rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
  congr 2
  ring

/-- **Lower bound for the radial family**: the metric `1 / |z|` gives `log (R / r) / (2π)`. -/
theorem ofReal_le_extLength_radialFamily {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (Real.log (R / r) / (2 * π)) ≤ extLength volume (radialFamily r R) := by
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have harea := rhoArea_annulusMetric hr hrR.le
  refine le_trans ?_ (ratio_le_extLength (measurable_annulusMetric r R) ?_)
  · have hmin : ENNReal.ofReal (Real.log (R / r)) ≤
        minLength (annulusMetric r R) (radialFamily r R) :=
      le_minLength fun μ hμ => by
        obtain ⟨θ, rfl⟩ := hμ
        exact (rhoLength_annulusMetric hr hrR.le θ).ge
    rw [harea]
    calc ENNReal.ofReal (Real.log (R / r) / (2 * π))
        = ENNReal.ofReal (Real.log (R / r)) ^ 2 /
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hlog.le,
            ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          field_simp
      _ ≤ minLength (annulusMetric r R) (radialFamily r R) ^ 2 /
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r))) := by gcongr
  · rw [harea]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The modulus of a round annulus** (radial form): the extremal length of the family of radial
segments of `{r < |z| < R}` is `log (R / r) / (2π)`. -/
theorem extLength_radialFamily {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extLength volume (radialFamily r R) = ENNReal.ofReal (Real.log (R / r) / (2 * π)) :=
  le_antisymm (extLength_le fun _ hρ _ => ratio_radialFamily_le hr hrR hρ)
    (ofReal_le_extLength_radialFamily hr hrR)

/-! ### The circle family -/

/-- The length measure of the circle `|z| = s`: its arc length `s dθ`. -/
def circleCurve (s : ℝ) : Measure ℂ :=
  ENNReal.ofReal s • (volume.restrict (Ioo (-π) π)).map fun θ : ℝ => pol (s, θ)

/-- The circles `|z| = s`, `r < s ≤ R`, of the annulus `{r < |z| < R}`: the curves that separate
its two boundary circles. -/
def circleFamily (r R : ℝ) : Set (Measure ℂ) := circleCurve '' Ioc r R

lemma measurable_pol_right (s : ℝ) : Measurable fun θ : ℝ => pol (s, θ) :=
  measurable_pol.comp (measurable_const.prodMk measurable_id)

lemma rhoLength_circleCurve {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (s : ℝ) :
    rhoLength ρ (circleCurve s) =
      ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, ρ (pol (s, θ)) := by
  unfold rhoLength circleCurve
  rw [lintegral_smul_measure, lintegral_map hρ (measurable_pol_right s), smul_eq_mul]

/-- Cauchy–Schwarz along a circle. -/
lemma circle_cs {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ θ in Ioo (-π) π, g θ) ^ 2 ≤
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, g θ ^ 2 := by
  have h := lintegral_mul_sq_le (volume.restrict (Ioo (-π) π)) (f := g) (g := fun _ => 1)
    hg.aemeasurable aemeasurable_const
  simp only [mul_one, one_pow, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioo, one_mul] at h
  rw [mul_comm]
  convert h using 3
  ring_nf

/-- **Upper bound for the circle family.** -/
theorem ratio_circleFamily_le {r R : ℝ} (hr : 0 < r) (hrR : r < R) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    minLength ρ (circleFamily r R) ^ 2 / rhoArea volume ρ ≤
      ENNReal.ofReal (2 * π / Real.log (R / r)) := by
  set L := minLength ρ (circleFamily r R) with hL
  set A := rhoArea volume ρ with hA
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have hs : ∀ s ∈ Ioc r R, ENNReal.ofReal s⁻¹ * L ^ 2 ≤
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 := by
    intro s hs
    have hs0 : 0 < s := hr.trans hs.1
    have hLle : L ≤ ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, ρ (pol (s, θ)) := by
      rw [← rhoLength_circleCurve hρ s]
      exact minLength_le_rhoLength ⟨s, hs, rfl⟩
    have hcs := circle_cs (hρ.comp (measurable_pol_right s))
    calc ENNReal.ofReal s⁻¹ * L ^ 2
        ≤ ENNReal.ofReal s⁻¹ * (ENNReal.ofReal s * ∫⁻ θ in Ioo (-π) π, ρ (pol (s, θ))) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal s * (∫⁻ θ in Ioo (-π) π, ρ (pol (s, θ))) ^ 2 := by
          rw [mul_pow, ← mul_assoc, ← ENNReal.ofReal_pow hs0.le, ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le)]
          congr 2
          field_simp
      _ ≤ ENNReal.ofReal s * (ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo (-π) π, ρ (pol (s, θ)) ^ 2) := by
          gcongr
          exact hcs
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          ring
  have hF : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ρ (pol p) ^ 2 :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul ((hρ.comp measurable_pol).pow_const 2)
  have hpolar : ∫⁻ s in Ioc r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 ≤ A := by
    calc ∫⁻ s in Ioc r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2
        ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 :=
          lintegral_mono' (Measure.restrict_mono (fun s hs => hr.trans hs.1) le_rfl) le_rfl
      _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * ρ (pol p) ^ 2 :=
          (lintegral_polar_rectangle' _ hF).symm
      _ = A := lintegral_polar fun z => ρ z ^ 2
  have hint : ENNReal.ofReal (Real.log (R / r)) * L ^ 2 ≤ ENNReal.ofReal (2 * π) * A := by
    calc ENNReal.ofReal (Real.log (R / r)) * L ^ 2
        = ∫⁻ s in Ioc r R, ENNReal.ofReal s⁻¹ * L ^ 2 := by
          have hmeas : Measurable fun s : ℝ => ENNReal.ofReal s⁻¹ :=
            ENNReal.measurable_ofReal.comp measurable_inv
          rw [lintegral_mul_const _ hmeas, lintegral_inv_Ioc hr hrR.le]
      _ ≤ ∫⁻ s in Ioc r R, ENNReal.ofReal (2 * π) *
            ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 :=
          setLIntegral_mono' measurableSet_Ioc hs
      _ = ENNReal.ofReal (2 * π) *
            ∫⁻ s in Ioc r R, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal s * ρ (pol (s, θ)) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 * π) * A := by gcongr
  have hlog0 : ENNReal.ofReal (Real.log (R / r)) ≠ 0 := by
    simp [hlog]
  rcases eq_or_ne A 0 with h0 | h0
  · rw [h0, mul_zero, nonpos_iff_eq_zero] at hint
    have : L ^ 2 = 0 := (mul_eq_zero.1 hint).resolve_left hlog0
    rw [this, h0]
    simp
  rcases eq_or_ne A ⊤ with htop | htop
  · rw [htop]
    simp
  rw [ENNReal.div_le_iff h0 htop]
  refine (ENNReal.mul_le_mul_iff_right hlog0 ENNReal.ofReal_ne_top).1 ?_
  calc ENNReal.ofReal (Real.log (R / r)) * L ^ 2
      ≤ ENNReal.ofReal (2 * π) * A := hint
    _ = ENNReal.ofReal (Real.log (R / r)) * (ENNReal.ofReal (2 * π / Real.log (R / r)) * A) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hlog.le, mul_div_cancel₀ _ hlog.ne']

/-- Every circle `|z| = s`, `r < s ≤ R`, has length `2π` for the metric `1 / |z|`. -/
lemma rhoLength_annulusMetric_circle {r R : ℝ} (hr : 0 < r) {s : ℝ} (hs : s ∈ Ioc r R) :
    rhoLength (annulusMetric r R) (circleCurve s) = ENNReal.ofReal (2 * π) := by
  have hs0 : 0 < s := hr.trans hs.1
  have hconst : ∀ θ : ℝ, annulusMetric r R (pol (s, θ)) = ENNReal.ofReal s⁻¹ := fun θ => by
    rw [annulusMetric_pol θ hs0.le, Set.indicator_of_mem hs]
  rw [rhoLength_circleCurve (measurable_annulusMetric r R)]
  simp only [hconst, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioo]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hs0.le, mul_inv_cancel₀ hs0.ne', ENNReal.ofReal_one,
    one_mul]
  congr 1
  ring

/-- **Lower bound for the circle family**: the metric `1 / |z|` gives `2π / log (R / r)`. -/
theorem ofReal_le_extLength_circleFamily {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (2 * π / Real.log (R / r)) ≤ extLength volume (circleFamily r R) := by
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  have harea := rhoArea_annulusMetric hr hrR.le
  refine le_trans ?_ (ratio_le_extLength (measurable_annulusMetric r R) ?_)
  · have hmin : ENNReal.ofReal (2 * π) ≤ minLength (annulusMetric r R) (circleFamily r R) :=
      le_minLength fun μ hμ => by
        obtain ⟨s, hs, rfl⟩ := hμ
        exact (rhoLength_annulusMetric_circle hr hs).ge
    rw [harea]
    calc ENNReal.ofReal (2 * π / Real.log (R / r))
        = ENNReal.ofReal (2 * π) ^ 2 /
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          field_simp
      _ ≤ minLength (annulusMetric r R) (circleFamily r R) ^ 2 /
            (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (R / r))) := by gcongr
  · rw [harea]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The modulus of a round annulus** (circle form): the extremal length of the family of
circles that separate the boundary circles of `{r < |z| < R}` is `2π / log (R / r)`. -/
theorem extLength_circleFamily {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extLength volume (circleFamily r R) = ENNReal.ofReal (2 * π / Real.log (R / r)) :=
  le_antisymm (extLength_le fun _ hρ _ => ratio_circleFamily_le hr hrR hρ)
    (ofReal_le_extLength_circleFamily hr hrR)

/-- The extremal length of the separating circles is the extremal width of the joining radial
segments, and conversely. -/
theorem extLength_circleFamily_eq_extWidth_radialFamily {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extLength volume (circleFamily r R) = extWidth volume (radialFamily r R) := by
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  rw [extWidth, extLength_radialFamily hr hrR, extLength_circleFamily hr hrR,
    ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-- Reciprocity: the extremal lengths of the joining and of the separating curves multiply to
`1`. -/
theorem extLength_radialFamily_mul_circleFamily {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    extLength volume (radialFamily r R) * extLength volume (circleFamily r R) = 1 := by
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).2 hrR)
  rw [extLength_radialFamily hr hrR, extLength_circleFamily hr hrR,
    ← ENNReal.ofReal_mul (by positivity)]
  have : Real.log (R / r) / (2 * π) * (2 * π / Real.log (R / r)) = 1 := by
    field_simp
  rw [this, ENNReal.ofReal_one]

/-! ### The series law for concentric annuli -/

/-- The radial segment of `{r < |z| < R}` lives on the annulus. -/
lemma radialCurve_compl_null {r R : ℝ} (hr : 0 < r) (θ : ℝ) :
    radialCurve r R θ {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ R}ᶜ = 0 := by
  have hmeas : MeasurableSet {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ R} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  unfold radialCurve
  rw [Measure.map_apply (measurable_pol_left θ) hmeas.compl, Measure.restrict_apply'
    measurableSet_Ioc]
  refine measure_mono_null (fun s hs => ?_) measure_empty
  obtain ⟨hs1, hs2⟩ := hs
  exact hs1 (by simpa [norm_pol (hr.trans hs2.1).le] using hs2)

/-- A radial segment of `{r < |z| < R'}` contains the radial segments of the same direction in two
concentric annuli `{r < |z| < R}` and `{r' < |z| < R'}`, `R ≤ r'`. -/
lemma radialCurve_add_le {r R r' R' : ℝ} (hrR : r ≤ R) (h : R ≤ r') (hr' : r' ≤ R') (θ : ℝ) :
    radialCurve r R θ + radialCurve r' R' θ ≤ radialCurve r R' θ := by
  have hdisj : Disjoint (Ioc r R) (Ioc r' R') :=
    Set.disjoint_left.2 fun s hs hs' => (not_le.2 hs'.1) (hs.2.trans h)
  unfold radialCurve
  rw [← Measure.map_add _ _ (measurable_pol_left θ),
    ← Measure.restrict_union hdisj measurableSet_Ioc]
  refine Measure.map_mono (Measure.restrict_mono ?_ le_rfl) (measurable_pol_left θ)
  rintro s (hs | hs)
  · exact ⟨hs.1, hs.2.trans (h.trans hr')⟩
  · exact ⟨hrR.trans_lt (h.trans_lt hs.1), hs.2⟩

/-- **The series law for concentric annuli.** The extremal lengths of the radial segments of
`{r < |z| < R}` and of `{r' < |z| < R'}`, `R ≤ r'`, add up to at most that of
`{r < |z| < R'}`: the series law of `ExtremalLength.lean`, Grötzsch's inequality, in the model. -/
theorem extLength_radialFamily_add_le {r R r' R' : ℝ} (hr : 0 < r) (hrR : r ≤ R) (h : R ≤ r')
    (hr' : r' ≤ R') :
    extLength volume (radialFamily r R) + extLength volume (radialFamily r' R') ≤
      extLength volume (radialFamily r R') := by
  have hr'0 : 0 < r' := hr.trans_le (hrR.trans h)
  have hmeas : ∀ a b : ℝ, MeasurableSet {z : ℂ | a < ‖z‖ ∧ ‖z‖ ≤ b} := fun a b =>
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  refine extLength_series (hmeas r R) (hmeas r' R') ?_ ?_ ?_ ?_
  · refine Set.disjoint_left.2 fun z hz hz' => ?_
    exact (not_le.2 hz'.1) (hz.2.trans h)
  · rintro μ ⟨θ, rfl⟩
    exact radialCurve_compl_null hr θ
  · rintro μ ⟨θ, rfl⟩
    exact radialCurve_compl_null hr'0 θ
  · rintro μ ⟨θ, rfl⟩
    exact ⟨radialCurve r R θ, ⟨θ, rfl⟩, radialCurve r' R' θ, ⟨θ, rfl⟩,
      radialCurve_add_le hrR h hr' θ⟩

end

end MLC.Research
