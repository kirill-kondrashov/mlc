import Mlc.Research.AnnulusModulus
import Mlc.Research.ParameterGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# From moduli of nested annuli to shrinking

`Mlc/Research/ParameterGeometry.lean` realizes a priori bounds by a `ConnectedNest` whose
`SeparationEstimate` says that the pieces shrink. This module proves the conformal-geometry
step behind that estimate, the Grötzsch–Teichmüller argument, from the abstract extremal length
of `Mlc/Research/ExtremalLength.lean`:

* a *loop* is a closed curve of class `C¹`; its length measure is its arc length
  (`loopMeasure`), and `loopFamily A K` is the family of the loops in `A` that go around every
  point of `K` (they meet every ray that starts in `K`);
* for a nest of pieces `P₀ ⊇ P₁ ⊇ …` around `c`, the loops in the annulus `Pⱼ ∖ cl P_{j+1}`
  around `cl P_{j+1}` form the family `D.loops j`, and the extremal width of this family is the
  modulus of the annulus (`extWidth`, `Mlc/Research/AnnulusModulus.lean` for the round case);
* **Theorem `ConnectedNest.sum_extWidth_loops_le`**: if the piece `P_n` reaches the distance
  `δ` from `c`, the moduli of the first `n` annuli add up to at most
  `2π log (4 (R + δ) / δ) / (2 log 2)²`, where `R` bounds the first piece. The proof combines
  the parallel law (the annuli are disjoint), and the metric `1 / |z - c|` truncated to
  `δ/2 ≤ |z - c| ≤ R + δ`, for which every loop has length at least `2 log 2`
  (`loop_length_ge`): a loop that stays outside the disk of radius `δ/2` goes around `c`, and a
  loop that enters it crosses the annulus `δ/2 ≤ |z - c| ≤ δ` twice;
* so the divergence of the sum of the moduli forces the pieces to shrink
  (`shrinking_of_moduli`) and gives a `ParameterRealization` for every budget
  (`ConnectedNest.parameterRealization`).

The estimates use the area inequality of Mathlib in dimension one
(`volume_image_le_lintegral_abs_deriv`) for the real functions `log |γ - c|` and `arg (γ - c)`.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Topology Metric

noncomputable section

/-! ### Loops -/

/-- A closed curve of class `C¹` with period `1`. -/
def IsLoop (γ : ℝ → ℂ) : Prop := ContDiff ℝ 1 γ ∧ Function.Periodic γ 1

/-- The length measure of a loop: its arc length, transported to the plane. -/
def loopMeasure (γ : ℝ → ℂ) : Measure ℂ :=
  ((volume.restrict (Ioc (0 : ℝ) 1)).withDensity fun t => ENNReal.ofReal ‖deriv γ t‖).map γ

lemma IsLoop.continuous {γ : ℝ → ℂ} (h : IsLoop γ) : Continuous γ := h.1.continuous

lemma IsLoop.continuous_deriv {γ : ℝ → ℂ} (h : IsLoop γ) : Continuous (deriv γ) :=
  h.1.continuous_deriv le_rfl

lemma IsLoop.hasDerivAt {γ : ℝ → ℂ} (h : IsLoop γ) (t : ℝ) : HasDerivAt γ (deriv γ t) t :=
  ((h.1.differentiable one_ne_zero) t).hasDerivAt

/-- The `ρ`-length of a loop is the integral of `ρ ∘ γ` against the speed. -/
lemma rhoLength_loopMeasure {γ : ℝ → ℂ} (hγ : IsLoop γ) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    rhoLength ρ (loopMeasure γ) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ρ (γ t) * ENNReal.ofReal ‖deriv γ t‖ := by
  have hd : Measurable fun t => ENNReal.ofReal ‖deriv γ t‖ :=
    ENNReal.measurable_ofReal.comp hγ.continuous_deriv.norm.measurable
  have hm : Measurable fun a => ρ (γ a) := hρ.comp hγ.continuous.measurable
  unfold rhoLength loopMeasure
  rw [lintegral_map hρ hγ.continuous.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hd hm (g := fun a => ρ (γ a))]
  exact lintegral_congr fun t => mul_comm _ _

/-- A time of a loop is equivalent to a time in `[0, 1]`. -/
lemma IsLoop.exists_mem_Icc {γ : ℝ → ℂ} (h : IsLoop γ) (t : ℝ) :
    ∃ t' ∈ Icc (0 : ℝ) 1, γ t' = γ t :=
  ⟨t - ⌊t⌋, ⟨sub_nonneg.2 (Int.floor_le t), (Int.fract_lt_one t).le⟩, by
    simpa using h.2.sub_int_mul_eq (x := t) ⌊t⌋⟩

/-! ### The area inequality in dimension one -/

/-- The image of a measurable set under a function that is differentiable on it has measure at most
the integral of the absolute value of the derivative. -/
lemma volume_image_le_lintegral_abs_deriv {f f' : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x) :
    volume (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |f' x| := by
  have h := addHaar_image_le_lintegral_abs_det_fderiv (volume : Measure ℝ) hs
    (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ (f' x))
    (fun x hx => (hf x hx).hasDerivWithinAt.hasFDerivWithinAt)
  simpa [ContinuousLinearMap.det_toSpanSingleton] using h

/-! ### Derivatives along a loop -/

section Derivatives

variable {γ : ℝ → ℂ} {c : ℂ}

/-- The derivative of `log |γ - c|` along a `C¹` curve that avoids `c`. -/
lemma hasDerivAt_log_norm_sub (hγ : IsLoop γ) (hne : ∀ t, γ t ≠ c) (t : ℝ) :
    HasDerivAt (fun t => Real.log ‖γ t - c‖)
      (inner ℝ (γ t - c) (deriv γ t) / ‖γ t - c‖ ^ 2) t := by
  have h1 : HasDerivAt (fun t => γ t - c) (deriv γ t) t := (hγ.hasDerivAt t).sub_const c
  have h2 := h1.norm_sq
  have hne' : ‖γ t - c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (hne t)))
  have h4 := (h2.log hne').const_mul (1 / 2 : ℝ)
  have hfun : (fun t => Real.log ‖γ t - c‖) = fun t => 1 / 2 * Real.log (‖γ t - c‖ ^ 2) := by
    funext t
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  convert h4 using 1
  field_simp

/-- The speed of `log |γ - c|` is at most the speed of `γ` over the distance to `c`. -/
lemma abs_deriv_log_norm_le (hne : ∀ t, γ t ≠ c) (t : ℝ) :
    |inner ℝ (γ t - c) (deriv γ t) / ‖γ t - c‖ ^ 2| ≤ ‖deriv γ t‖ / ‖γ t - c‖ := by
  have hpos : 0 < ‖γ t - c‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne t))
  rw [abs_div, abs_of_pos (pow_pos hpos 2), div_le_div_iff₀ (pow_pos hpos 2) hpos]
  have h := abs_real_inner_le_norm (γ t - c) (deriv γ t)
  calc |inner ℝ (γ t - c) (deriv γ t)| * ‖γ t - c‖
      ≤ (‖γ t - c‖ * ‖deriv γ t‖) * ‖γ t - c‖ := by gcongr
    _ = ‖deriv γ t‖ * ‖γ t - c‖ ^ 2 := by ring

/-- The derivative of `arg (γ - c)` where `γ - c` is off the negative real axis. -/
lemma hasDerivAt_arg_sub (hγ : IsLoop γ) {t : ℝ} (ht : γ t - c ∈ Complex.slitPlane) :
    HasDerivAt (fun t => Complex.arg (γ t - c)) ((deriv γ t / (γ t - c)).im) t := by
  have h1 : HasDerivAt (fun t => γ t - c) (deriv γ t) t := (hγ.hasDerivAt t).sub_const c
  have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (h1.clog_real ht)
  simpa [Function.comp_def, Complex.log_im] using h3

/-- The speed of `arg (γ - c)` is at most the speed of `γ` over the distance to `c`. -/
lemma abs_im_div_le (w v : ℂ) : |(v / w).im| ≤ ‖v‖ / ‖w‖ :=
  (Complex.abs_im_le_norm _).trans (by rw [norm_div])

end Derivatives

/-! ### The metric `1 / |z - c|` on a ring -/

/-- The metric `1 / |z - c|` on the closed ring `r ≤ |z - c| ≤ R`. -/
def ringMetric (c : ℂ) (r R : ℝ) (z : ℂ) : ℝ≥0∞ :=
  if r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R then ENNReal.ofReal ‖z - c‖⁻¹ else 0

lemma measurable_ringMetric (c : ℂ) (r R : ℝ) : Measurable (ringMetric c r R) := by
  have hn : Measurable fun z : ℂ => ‖z - c‖ := (measurable_id.sub_const c).norm
  unfold ringMetric
  exact Measurable.ite ((measurableSet_le measurable_const hn).inter
    (measurableSet_le hn measurable_const)) (ENNReal.measurable_ofReal.comp hn.inv) measurable_const

/-- The area of the metric `1 / |z - c|` on the ring `r ≤ |z - c| ≤ R`. -/
lemma rhoArea_ringMetric_le (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    rhoArea volume (ringMetric c r R) ≤
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (2 * R / r)) := by
  have hr2 : 0 < r / 2 := by positivity
  have hle : ∀ z, ringMetric c r R z ≤ annulusMetric (r / 2) R (z - c) := by
    intro z
    unfold ringMetric annulusMetric
    by_cases h : r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R
    · have h' : r / 2 < ‖z - c‖ ∧ ‖z - c‖ ≤ R := ⟨by linarith [h.1], h.2⟩
      simp [h, h']
    · simp [h]
  calc rhoArea volume (ringMetric c r R)
      ≤ rhoArea volume (fun z => annulusMetric (r / 2) R (z - c)) :=
        lintegral_mono fun z => pow_le_pow_left' (hle z) 2
    _ = rhoArea volume (annulusMetric (r / 2) R) :=
        lintegral_sub_right_eq_self (fun z => annulusMetric (r / 2) R z ^ 2) c
    _ = _ := by
        rw [rhoArea_annulusMetric hr2 (by linarith)]
        have : R / (r / 2) = 2 * R / r := by field_simp
        rw [this]

/-! ### The length of a loop in the ring metric -/

section Length

variable {γ : ℝ → ℂ} {c : ℂ}

/-- The `ρ`-length of a loop is at least the measure of the image of a set of times under a
function whose speed is at most the speed of the loop over the distance to `c`, where
`ρ = 1 / |z - c|`. -/
lemma volume_le_rhoLength_loopMeasure (hγ : IsLoop γ) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS01 : S ⊆ Icc (0 : ℝ) 1)
    (hρS : ∀ t ∈ S, ρ (γ t) = ENNReal.ofReal ‖γ t - c‖⁻¹)
    {f f' : ℝ → ℝ} (hf : ∀ t ∈ S, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ S, |f' t| ≤ ‖deriv γ t‖ / ‖γ t - c‖) {I : Set ℝ} (hI : I ⊆ f '' S) :
    volume I ≤ rhoLength ρ (loopMeasure γ) := by
  rw [rhoLength_loopMeasure hγ hρ]
  calc volume I ≤ volume (f '' S) := measure_mono hI
    _ ≤ ∫⁻ t in S, ENNReal.ofReal |f' t| := volume_image_le_lintegral_abs_deriv hS hf
    _ ≤ ∫⁻ t in S, ρ (γ t) * ENNReal.ofReal ‖deriv γ t‖ := by
        refine setLIntegral_mono' hS fun t ht => ?_
        rw [hρS t ht, ← ENNReal.ofReal_mul (inv_nonneg.2 (norm_nonneg _))]
        exact ENNReal.ofReal_le_ofReal ((hf' t ht).trans (by rw [div_eq_inv_mul]))
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ρ (γ t) * ENNReal.ofReal ‖deriv γ t‖ := lintegral_mono_set hS01
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ρ (γ t) * ENNReal.ofReal ‖deriv γ t‖ :=
        (setLIntegral_congr Ioc_ae_eq_Icc).symm

/-- A loop that goes around `c` outside the disk of radius `r` has `ρ`-length at least `2π`: the
argument of `γ - c` sweeps the interval `(-π, π)`. -/
lemma two_pi_le_rhoLength (hγ : IsLoop γ) {r R : ℝ} (hr : 0 < r)
    (hout : ∀ t, r ≤ ‖γ t - c‖) (hin : ∀ t, ‖γ t - c‖ ≤ R)
    (hcover : ∀ u : ℂ, ‖u‖ = 1 → ∃ t : ℝ, ∃ s : ℝ, 0 < s ∧ γ t = c + (s : ℂ) * u) :
    ENNReal.ofReal (2 * π) ≤ rhoLength (ringMetric c r R) (loopMeasure γ) := by
  have hne : ∀ t, γ t - c ≠ 0 := fun t => norm_pos_iff.1 (hr.trans_le (hout t))
  have hS : MeasurableSet {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ γ t - c ∈ Complex.slitPlane} :=
    measurableSet_Icc.inter
      (Complex.isOpen_slitPlane.preimage (hγ.continuous.sub continuous_const)).measurableSet
  have hI : Ioo (-π) π ⊆ (fun t => Complex.arg (γ t - c)) ''
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ γ t - c ∈ Complex.slitPlane} := by
    intro θ hθ
    obtain ⟨t₀, s, hs, hγt⟩ := hcover (Complex.exp (θ * Complex.I))
      (Complex.norm_exp_ofReal_mul_I θ)
    obtain ⟨t, ht01, hγtt⟩ := hγ.exists_mem_Icc t₀
    have hw : γ t - c = (s : ℂ) * Complex.exp (θ * Complex.I) := by rw [hγtt, hγt]; ring
    have harg : Complex.arg (γ t - c) = θ := by
      rw [hw, Complex.arg_real_mul _ hs, Complex.arg_exp_mul_I,
        (toIocMod_eq_self Real.two_pi_pos).2 ⟨hθ.1, by linarith [hθ.2]⟩]
    exact ⟨t, ⟨ht01, Complex.mem_slitPlane_iff_arg.2 ⟨by rw [harg]; exact hθ.2.ne, hne t⟩⟩, harg⟩
  have h := volume_le_rhoLength_loopMeasure hγ (measurable_ringMetric c r R) hS
    (fun t ht => ht.1) (c := c)
    (fun t _ => by simp [ringMetric, hout t, hin t])
    (fun t ht => hasDerivAt_arg_sub hγ ht.2)
    (fun t _ => abs_im_div_le (γ t - c) (deriv γ t)) hI
  rwa [Real.volume_Ioo, show π - -π = 2 * π by ring] at h

/-- A loop that meets the disk of radius `r` around `c` and reaches the distance `2r` has
`ρ`-length at least `log 2`: it crosses the ring `r ≤ |z - c| ≤ 2r`. -/
lemma log_two_le_rhoLength (hγ : IsLoop γ) {r R : ℝ} (hr : 0 < r) (h2r : 2 * r ≤ R)
    (hne : ∀ t, γ t ≠ c) {a b : ℝ} (ha : ‖γ a - c‖ < r) (hb : 2 * r < ‖γ b - c‖) :
    ENNReal.ofReal (Real.log 2) ≤ rhoLength (ringMetric c r R) (loopMeasure γ) := by
  obtain ⟨a', ha01, hγa⟩ := hγ.exists_mem_Icc a
  obtain ⟨b', hb01, hγb⟩ := hγ.exists_mem_Icc b
  rw [← hγa] at ha
  rw [← hγb] at hb
  have hpos : ∀ t, 0 < ‖γ t - c‖ := fun t => norm_pos_iff.2 (sub_ne_zero.2 (hne t))
  have hfc : Continuous fun t => Real.log ‖γ t - c‖ :=
    (hγ.continuous.sub continuous_const).norm.log fun t => (hpos t).ne'
  set S : Set ℝ := uIcc a' b' ∩ (fun t => Real.log ‖γ t - c‖) ⁻¹'
    Icc (Real.log r) (Real.log (2 * r)) with hSdef
  have hS : MeasurableSet S := measurableSet_uIcc.inter (hfc.measurable measurableSet_Icc)
  have hS01 : S ⊆ Icc (0 : ℝ) 1 := fun t ht => uIcc_subset_Icc ha01 hb01 ht.1
  have hρS : ∀ t ∈ S, ringMetric c r R (γ t) = ENNReal.ofReal ‖γ t - c‖⁻¹ := by
    intro t ht
    have h1 := ht.2.1
    have h2 := ht.2.2
    have hl : r ≤ ‖γ t - c‖ := (Real.log_le_log_iff hr (hpos t)).1 h1
    have hu : ‖γ t - c‖ ≤ 2 * r := (Real.log_le_log_iff (hpos t) (by positivity)).1 h2
    simp [ringMetric, hl, hu.trans h2r]
  have hI : Icc (Real.log r) (Real.log (2 * r)) ⊆ (fun t => Real.log ‖γ t - c‖) '' S := by
    intro y hy
    have hfa : Real.log ‖γ a' - c‖ < Real.log r := Real.log_lt_log (hpos a') ha
    have hfb : Real.log (2 * r) < Real.log ‖γ b' - c‖ := Real.log_lt_log (by positivity) hb
    have hy' : y ∈ uIcc (Real.log ‖γ a' - c‖) (Real.log ‖γ b' - c‖) :=
      Set.mem_uIcc.2 (Or.inl ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    obtain ⟨t, ht, hty⟩ := intermediate_value_uIcc hfc.continuousOn hy'
    have hty' : Real.log ‖γ t - c‖ = y := hty
    exact ⟨t, ⟨ht, show Real.log ‖γ t - c‖ ∈ Icc (Real.log r) (Real.log (2 * r)) by
      rw [hty']; exact hy⟩, hty⟩
  have h := volume_le_rhoLength_loopMeasure hγ (measurable_ringMetric c r R) hS hS01 (c := c)
    hρS (fun t _ => hasDerivAt_log_norm_sub hγ hne t)
    (fun t _ => abs_deriv_log_norm_le hne t) hI
  rwa [Real.volume_Icc, Real.log_mul two_ne_zero hr.ne', add_sub_cancel_right] at h

/-- Every `C¹` loop that avoids `c`, goes around `c` and reaches the distance `2r` has `ρ`-length
at least `log 2`, for the metric `1 / |z - c|` on the ring `r ≤ |z - c| ≤ R`. -/
lemma log_two_le_rhoLength_of_cover (hγ : IsLoop γ) {r R : ℝ} (hr : 0 < r) (h2r : 2 * r ≤ R)
    (hne : ∀ t, γ t ≠ c) (hin : ∀ t, ‖γ t - c‖ ≤ R)
    (hcover : ∀ u : ℂ, ‖u‖ = 1 → ∃ t : ℝ, ∃ s : ℝ, 0 < s ∧ γ t = c + (s : ℂ) * u)
    {b : ℝ} (hb : 2 * r < ‖γ b - c‖) :
    ENNReal.ofReal (Real.log 2) ≤ rhoLength (ringMetric c r R) (loopMeasure γ) := by
  by_cases hout : ∀ t, r ≤ ‖γ t - c‖
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (two_pi_le_rhoLength hγ hr hout hin hcover)
    linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2), Real.two_le_pi]
  · obtain ⟨a, ha⟩ := not_forall.1 hout
    exact log_two_le_rhoLength hγ hr h2r hne (not_le.1 ha) hb

end Length

/-! ### The annuli of a nest -/

/-- The family of the `C¹` loops in `A` that go around every point of `K`: each ray that starts in
`K` meets the loop. A loop is recorded by its length measure. -/
def loopFamily (A K : Set ℂ) : Set (Measure ℂ) :=
  {μ | ∃ γ : ℝ → ℂ, IsLoop γ ∧ (∀ t, γ t ∈ A) ∧
    (∀ z ∈ K, ∀ u : ℂ, ‖u‖ = 1 → ∃ t : ℝ, ∃ s : ℝ, 0 < s ∧ γ t = z + (s : ℂ) * u) ∧
    μ = loopMeasure γ}

/-- The length measure of a loop in `A` vanishes outside `A`. -/
lemma loopMeasure_compl_eq_zero {γ : ℝ → ℂ} (hγ : IsLoop γ) {A : Set ℂ} (hA : MeasurableSet A)
    (h : ∀ t, γ t ∈ A) : loopMeasure γ Aᶜ = 0 := by
  unfold loopMeasure
  rw [Measure.map_apply hγ.continuous.measurable hA.compl]
  have : γ ⁻¹' Aᶜ = ∅ := by
    ext t
    simp [h t]
  rw [this, measure_empty]

/-- The ray from `z` that points away from `c` stays at distance `|z - c| + s` from `c`. -/
lemma exists_unit_norm_add {z c : ℂ} (hz : z ≠ c) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ s : ℝ, 0 < s → ‖z + (s : ℂ) * u - c‖ = ‖z - c‖ + s := by
  have hpos : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hne : ((‖z - c‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  refine ⟨((‖z - c‖ : ℝ) : ℂ)⁻¹ * (z - c), ?_, fun s hs => ?_⟩
  · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact inv_mul_cancel₀ hpos.ne'
  · have h : z + (s : ℂ) * (((‖z - c‖ : ℝ) : ℂ)⁻¹ * (z - c)) - c =
        ((1 + s / ‖z - c‖ : ℝ) : ℂ) * (z - c) := by
      push_cast
      field_simp
      ring
    rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp

namespace ConnectedNest

variable {S : Set ℂ} {c : ℂ} (D : ConnectedNest S c)

/-- The `j`-th annulus of the nest: the piece `j` without the closure of the piece `j + 1`. -/
def annulus (j : ℕ) : Set ℂ := D.piece j \ closure (D.piece (j + 1))

/-- The loops of the `j`-th annulus that go around the closure of the next piece. Their extremal
width is the modulus of the annulus. -/
def loops (j : ℕ) : Set (Measure ℂ) := loopFamily (D.annulus j) (closure (D.piece (j + 1)))

lemma antitone_piece : Antitone D.piece := antitone_nat_of_succ_le D.nested

lemma measurableSet_annulus (j : ℕ) : MeasurableSet (D.annulus j) :=
  (D.open_piece j).measurableSet.diff isClosed_closure.measurableSet

lemma disjoint_annulus {i j : ℕ} (h : i < j) : Disjoint (D.annulus i) (D.annulus j) :=
  Set.disjoint_left.2 fun _ hzi hzj => hzi.2 (subset_closure (D.antitone_piece h hzj.1))

lemma pairwiseDisjoint_annulus (s : Set ℕ) : s.PairwiseDisjoint D.annulus := by
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact D.disjoint_annulus h
  · exact (D.disjoint_annulus h).symm

lemma loops_compl_null {j : ℕ} {μ : Measure ℂ} (hμ : μ ∈ D.loops j) :
    μ (D.annulus j)ᶜ = 0 := by
  obtain ⟨γ, hγ, hA, -, rfl⟩ := hμ
  exact loopMeasure_compl_eq_zero hγ (D.measurableSet_annulus j) hA

/-- **The moduli of the annuli of a nest add up to a bounded amount while the nest keeps a point
at distance `δ` from `c`.** The first piece lies in the disk of radius `R` around `c`. The sum of
the extremal widths of the first `n` annuli is at most
`2π log (4 (R + δ) / δ) / (log 2)²` if the closure of the piece `n` contains a point at distance at
least `δ` from `c`.

Each loop of an annulus avoids `c` and goes around `c` and around that point, so it has length at
least `log 2` for the metric `1 / |z - c|` on the ring `δ/2 ≤ |z - c| ≤ R + δ`, whose area is at
most `2π log (4 (R + δ) / δ)`; the annuli are disjoint, which gives the parallel law. -/
theorem sum_extWidth_loops_le {R δ : ℝ} (hδ : 0 < δ) (hR : closure (D.piece 0) ⊆ closedBall c R)
    {n : ℕ} {z : ℂ} (hz : z ∈ closure (D.piece n)) (hzδ : δ ≤ dist z c) :
    ∑ j ∈ Finset.range n, extWidth volume (D.loops j) ≤
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (4 * (R + δ) / δ)) /
        ENNReal.ofReal (Real.log 2) ^ 2 := by
  have hR0 : 0 ≤ R := dist_nonneg.trans (mem_closedBall.1 (hR (D.mem_closure 0)))
  have hr : 0 < δ / 2 := by positivity
  have h2r : 2 * (δ / 2) ≤ R + δ := by linarith
  have hrR : δ / 2 ≤ R + δ := by linarith
  have hzc : z ≠ c := fun h => by
    rw [h, dist_self] at hzδ
    linarith
  have hzδ' : δ ≤ ‖z - c‖ := by rwa [dist_eq_norm] at hzδ
  refine (extWidth_parallel_finset (m := volume) (Finset.range n) (Γ := D.loops)
    (Ω := D.annulus) (fun j _ => D.measurableSet_annulus j) (D.pairwiseDisjoint_annulus _)
    (fun j _ μ hμ => D.loops_compl_null hμ)).trans ?_
  have hlen : ENNReal.ofReal (Real.log 2) ≤
      minLength (ringMetric c (δ / 2) (R + δ)) (⋃ j ∈ Finset.range n, D.loops j) := by
    refine le_minLength fun μ hμ => ?_
    obtain ⟨j, hj, hμj⟩ := Set.mem_iUnion₂.1 hμ
    obtain ⟨γ, hγ, hA, hcov, rfl⟩ := hμj
    have hjn : j + 1 ≤ n := Finset.mem_range.1 hj
    have hzj : z ∈ closure (D.piece (j + 1)) := closure_mono (D.antitone_piece hjn) hz
    have hcj : c ∈ closure (D.piece (j + 1)) := D.mem_closure (j + 1)
    have hne : ∀ t, γ t ≠ c := fun t h => (hA t).2 (h ▸ hcj)
    have hin : ∀ t, ‖γ t - c‖ ≤ R + δ := fun t => by
      have h := mem_closedBall.1 (hR (closure_mono (D.antitone_piece (Nat.zero_le j))
        (subset_closure (hA t).1)))
      rw [dist_eq_norm] at h
      linarith
    obtain ⟨u, hu, hnorm⟩ := exists_unit_norm_add hzc
    obtain ⟨b, s, hs, hγb⟩ := hcov z hzj u hu
    refine log_two_le_rhoLength_of_cover hγ hr h2r hne hin (hcov c hcj) (b := b) ?_
    rw [hγb, hnorm s hs]
    linarith
  have harea : rhoArea volume (ringMetric c (δ / 2) (R + δ)) ≤
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (4 * (R + δ) / δ)) := by
    refine (rhoArea_ringMetric_le c hr hrR).trans (le_of_eq ?_)
    rw [show 2 * (R + δ) / (δ / 2) = 4 * (R + δ) / δ by field_simp; ring]
  have hfin : ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (4 * (R + δ) / δ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hκ : ENNReal.ofReal (Real.log 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ENNReal.ofReal_pos.2 (Real.log_pos one_lt_two)).ne'
  have h1 := ratio_le_extLength (m := volume) (Γ := ⋃ j ∈ Finset.range n, D.loops j)
    (measurable_ringMetric c (δ / 2) (R + δ)) (harea.trans_lt hfin.lt_top)
  have h2 := le_trans (ENNReal.div_le_div (pow_le_pow_left' hlen 2) harea) h1
  unfold extWidth
  refine (ENNReal.inv_le_inv.2 h2).trans (le_of_eq ?_)
  rw [ENNReal.inv_div (Or.inl hfin) (Or.inr hκ)]

/-- The extremal widths of the annuli of the nest add up to infinity: the moduli of the annuli
have an infinite sum. -/
def DivergentModuli : Prop :=
  ∀ C : ℝ≥0∞, C ≠ ⊤ → ∃ n, C < ∑ j ∈ Finset.range n, extWidth volume (D.loops j)

/-- A uniform lower bound for the moduli of the annuli makes the sum of the moduli infinite. -/
theorem divergentModuli_of_uniform {w : ℝ≥0∞} (hw : w ≠ 0)
    (hmod : ∀ j, w ≤ extWidth volume (D.loops j)) : D.DivergentModuli := fun C hC => by
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hw hC
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  calc (n : ℝ≥0∞) * w = ∑ _j ∈ Finset.range n, w := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => hmod j

/-- **If the moduli of the annuli add up to infinity, the pieces shrink to `c`.** -/
theorem DivergentModuli.shrinking {D : ConnectedNest S c} (h : D.DivergentModuli) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ n, N ≤ n → closure (D.piece n) ⊆ ball c ε := by
  obtain ⟨R, hR⟩ := (D.compact_closure 0).isBounded.subset_closedBall c
  obtain ⟨N, hN⟩ := h (ENNReal.ofReal (2 * π) * ENNReal.ofReal (Real.log (4 * (R + ε) / ε)) /
    ENNReal.ofReal (Real.log 2) ^ 2) (by
      refine ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top) ?_
      exact pow_ne_zero 2 (ENNReal.ofReal_pos.2 (Real.log_pos one_lt_two)).ne')
  refine ⟨N, fun n hn z hz => ?_⟩
  by_contra hzε
  have h := D.sum_extWidth_loops_le hε hR hz (not_lt.1 (mem_ball.not.1 hzε))
  exact absurd (lt_of_lt_of_le hN (Finset.sum_le_sum_of_subset (Finset.range_mono hn)))
    (not_lt.2 h)

/-- Shrinking pieces satisfy the separation estimate for every cost sequence. -/
theorem separationEstimate_of_shrinking
    (hshr : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → closure (D.piece n) ⊆ ball c ε)
    (cost : ℕ → ℝ) : D.SeparationEstimate cost := by
  intro ε hε
  obtain ⟨N, hN⟩ := hshr ε hε
  refine ⟨∑ j ∈ Finset.range N, |cost j|, fun n z hz hzε => ?_⟩
  have hnN : n < N := by
    by_contra h
    exact absurd (mem_ball.1 (hN n (not_lt.1 h) hz)) (not_lt.2 hzε)
  calc ∑ j ∈ Finset.range n, cost j ≤ ∑ j ∈ Finset.range n, |cost j| :=
        Finset.sum_le_sum fun j _ => le_abs_self _
    _ ≤ ∑ j ∈ Finset.range N, |cost j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnN.le)
          fun j _ _ => abs_nonneg _

/-- A nest whose annuli have moduli with an infinite sum realizes every budget: the pieces
shrink, so the separation estimate holds for every cost. -/
theorem nonempty_parameterRealization (h : D.DivergentModuli) (b : ReturnBudget) :
    Nonempty (ParameterRealization S c b) :=
  ⟨⟨D, D.separationEstimate_of_shrinking (fun _ hε => h.shrinking hε) b.cost⟩⟩

end ConnectedNest

end

end MLC.Research
