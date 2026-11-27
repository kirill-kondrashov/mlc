import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Extremal length

A curve is represented by its length measure `μ`: a metric `ρ` gives it the length `∫ ρ dμ`.
Only length measures enter, so the theory needs no topology on the underlying space. The area
of a metric is `∫ ρ² dm` for an area measure `m`, and the extremal length of a family `Γ` of
curves is the supremum, over measurable metrics `ρ` of finite area, of
`(inf_{μ ∈ Γ} ∫ ρ dμ)² / ∫ ρ² dm`.

The file proves the conformal-geometry foundation used by the survey of Dudko
(arXiv:2512.24171):

* comparison (`extLength_mono`): if each curve of `Γ` contains a curve of `Γ'`, then `Γ'` has the
  smaller extremal length;
* the series law, that is the Grötzsch inequality (`extLength_series`): curves that cross two
  disjoint regions in succession have extremal length at least the sum;
* the parallel law (`extWidth_parallel`, and `extWidth_parallel_finset` for finitely many
  families): the extremal widths of families that live in pairwise disjoint regions add up;
* the arithmetic of estimate (4.6) (`extLength_complement_le`, `extWidth_ge_of_complement`,
  and `extWidth_ge_of_series` from a series decomposition): if the second piece of a series
  decomposition carries the fraction `1 - δ` of the extremal length, the first piece carries
  at most the fraction `δ`, so its width is at least `δ⁻¹` times the total width;
* the pullback law (`extLength_pullback_le`, `extWidth_pullback_le`): if a map `φ` carries the
  curves of `ΓX` to curves of `ΓY`, and the area elements satisfy `φ_*(J² mX) ≤ d · mY`,
  then `W(ΓX) ≤ d · W(ΓY)`. For a holomorphic map of degree `d` this is the estimate behind
  the Teichmüller contraction, and for `d = 1` it is conformal invariance.

All quantities take values in `ℝ≥0∞`, so the statements carry no finiteness or positivity
hypotheses on the families or on the metrics.
-/

namespace MLC.Research

open MeasureTheory ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The `ρ`-length of a curve with length measure `μ`. -/
def rhoLength (ρ : α → ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ := ∫⁻ x, ρ x ∂μ

/-- The `ρ`-area. -/
def rhoArea (m : Measure α) (ρ : α → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, ρ x ^ 2 ∂m

/-- The least `ρ`-length of a family of curves. -/
def minLength (ρ : α → ℝ≥0∞) (Γ : Set (Measure α)) : ℝ≥0∞ := ⨅ μ ∈ Γ, rhoLength ρ μ

/-- Extremal length of a family `Γ` of curves (each curve is its length measure), for the area
measure `m`. Metrics of area zero are allowed; they give the value `⊤` exactly when the least
length is positive. -/
def extLength (m : Measure α) (Γ : Set (Measure α)) : ℝ≥0∞ :=
  ⨆ (ρ : α → ℝ≥0∞) (_ : Measurable ρ) (_ : rhoArea m ρ < ⊤),
    minLength ρ Γ ^ 2 / rhoArea m ρ

/-- Extremal width: the reciprocal of the extremal length. -/
def extWidth (m : Measure α) (Γ : Set (Measure α)) : ℝ≥0∞ := (extLength m Γ)⁻¹

section Basic

variable {m : Measure α} {ρ : α → ℝ≥0∞} {Γ Γ' : Set (Measure α)}

lemma rhoLength_mono {μ ν : Measure α} (h : μ ≤ ν) (ρ : α → ℝ≥0∞) :
    rhoLength ρ μ ≤ rhoLength ρ ν :=
  lintegral_mono' h le_rfl

lemma rhoLength_add (ρ : α → ℝ≥0∞) (μ ν : Measure α) :
    rhoLength ρ (μ + ν) = rhoLength ρ μ + rhoLength ρ ν :=
  lintegral_add_measure ρ μ ν

lemma rhoArea_zero (m : Measure α) : rhoArea m (0 : α → ℝ≥0∞) = 0 := by
  simp [rhoArea]

lemma minLength_le_rhoLength {μ : Measure α} (hμ : μ ∈ Γ) : minLength ρ Γ ≤ rhoLength ρ μ :=
  iInf₂_le μ hμ

lemma le_minLength {c : ℝ≥0∞} (h : ∀ μ ∈ Γ, c ≤ rhoLength ρ μ) : c ≤ minLength ρ Γ :=
  le_iInf₂ h

lemma minLength_anti (h : Γ' ⊆ Γ) : minLength ρ Γ ≤ minLength ρ Γ' :=
  le_minLength fun _ hμ => minLength_le_rhoLength (h hμ)

/-- Each admissible metric gives a lower bound for the extremal length. -/
lemma ratio_le_extLength (hρ : Measurable ρ) (hA : rhoArea m ρ < ⊤) :
    minLength ρ Γ ^ 2 / rhoArea m ρ ≤ extLength m Γ :=
  le_iSup₂_of_le ρ hρ (le_iSup_of_le hA le_rfl)

/-- An upper bound for the quotients of all admissible metrics bounds the extremal length. -/
lemma extLength_le {c : ℝ≥0∞}
    (h : ∀ ρ : α → ℝ≥0∞, Measurable ρ → rhoArea m ρ < ⊤ →
      minLength ρ Γ ^ 2 / rhoArea m ρ ≤ c) : extLength m Γ ≤ c :=
  iSup₂_le fun ρ hρ => iSup_le fun hA => h ρ hρ hA

lemma extLength_eq_biSup (m : Measure α) (Γ : Set (Measure α)) :
    extLength m Γ = ⨆ ρ ∈ {ρ : α → ℝ≥0∞ | Measurable ρ ∧ rhoArea m ρ < ⊤},
      minLength ρ Γ ^ 2 / rhoArea m ρ := by
  simp only [extLength, Set.mem_setOf_eq, iSup_and]

/-- A bound for the sums of quotients of pairs of admissible metrics bounds the sum of two
extremal lengths. -/
lemma extLength_add_le {Γ₁ Γ₂ : Set (Measure α)} {c : ℝ≥0∞}
    (h : ∀ ρ₁ ρ₂ : α → ℝ≥0∞, Measurable ρ₁ → rhoArea m ρ₁ < ⊤ → Measurable ρ₂ →
      rhoArea m ρ₂ < ⊤ → minLength ρ₁ Γ₁ ^ 2 / rhoArea m ρ₁ +
        minLength ρ₂ Γ₂ ^ 2 / rhoArea m ρ₂ ≤ c) :
    extLength m Γ₁ + extLength m Γ₂ ≤ c := by
  rw [extLength_eq_biSup, extLength_eq_biSup]
  have h0 : (0 : α → ℝ≥0∞) ∈ {ρ : α → ℝ≥0∞ | Measurable ρ ∧ rhoArea m ρ < ⊤} :=
    ⟨measurable_zero, by simp [rhoArea_zero]⟩
  exact ENNReal.biSup_add_biSup_le ⟨0, h0⟩ ⟨0, h0⟩ fun ρ₁ hρ₁ ρ₂ hρ₂ =>
    h ρ₁ ρ₂ hρ₁.1 hρ₁.2 hρ₂.1 hρ₂.2

lemma minLength_le_of_dominates (ρ : α → ℝ≥0∞) {Γ Γ' : Set (Measure α)}
    (h : ∀ μ ∈ Γ, ∃ ν ∈ Γ', ν ≤ μ) : minLength ρ Γ' ≤ minLength ρ Γ :=
  le_minLength fun μ hμ => by
    obtain ⟨ν, hν, hle⟩ := h μ hμ
    exact (minLength_le_rhoLength hν).trans (rhoLength_mono hle ρ)

end Basic

/-- Comparison: if every curve of `Γ` contains a curve of `Γ'` (its length measure dominates), then
`Γ'` has the smaller extremal length. -/
theorem extLength_mono {m : Measure α} {Γ Γ' : Set (Measure α)}
    (h : ∀ μ ∈ Γ, ∃ ν ∈ Γ', ν ≤ μ) : extLength m Γ' ≤ extLength m Γ := by
  refine extLength_le fun ρ hρ hA => le_trans ?_ (ratio_le_extLength hρ hA)
  gcongr
  exact minLength_le_of_dominates ρ h

section Series

/-- The metric that equals `c₁ ρ₁` on `Ω₁` and `c₂ ρ₂` on `Ω₂`, and vanishes elsewhere. -/
def gluedMetric (Ω₁ Ω₂ : Set α) (c₁ c₂ : ℝ≥0∞) (ρ₁ ρ₂ : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  fun x => Ω₁.indicator (fun y => c₁ * ρ₁ y) x + Ω₂.indicator (fun y => c₂ * ρ₂ y) x

variable {Ω₁ Ω₂ : Set α} {c₁ c₂ : ℝ≥0∞} {ρ₁ ρ₂ : α → ℝ≥0∞}

lemma measurable_gluedMetric (hΩ₁ : MeasurableSet Ω₁) (hΩ₂ : MeasurableSet Ω₂)
    (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂) :
    Measurable (gluedMetric Ω₁ Ω₂ c₁ c₂ ρ₁ ρ₂) :=
  ((hρ₁.const_mul c₁).indicator hΩ₁).add ((hρ₂.const_mul c₂).indicator hΩ₂)

lemma lintegral_indicator_of_compl_null {Ω : Set α} {μ : Measure α} (h : μ Ωᶜ = 0)
    (f : α → ℝ≥0∞) : ∫⁻ x, Ω.indicator f x ∂μ = ∫⁻ x, f x ∂μ :=
  lintegral_congr_ae <| by
    filter_upwards [mem_ae_iff.2 h] with x hx using Set.indicator_of_mem hx f

/-- On curves that live in `Ω₁` and `Ω₂`, the glued metric has at least the weighted lengths. -/
lemma rhoLength_gluedMetric_ge (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    {μ₁ μ₂ : Measure α} (h₁ : μ₁ Ω₁ᶜ = 0) (h₂ : μ₂ Ω₂ᶜ = 0) :
    c₁ * rhoLength ρ₁ μ₁ + c₂ * rhoLength ρ₂ μ₂ ≤
      rhoLength (gluedMetric Ω₁ Ω₂ c₁ c₂ ρ₁ ρ₂) (μ₁ + μ₂) := by
  rw [rhoLength_add]
  refine add_le_add ?_ ?_
  · calc c₁ * rhoLength ρ₁ μ₁ = ∫⁻ x, Ω₁.indicator (fun y => c₁ * ρ₁ y) x ∂μ₁ := by
          rw [lintegral_indicator_of_compl_null h₁, rhoLength, lintegral_const_mul c₁ hρ₁]
      _ ≤ rhoLength (gluedMetric Ω₁ Ω₂ c₁ c₂ ρ₁ ρ₂) μ₁ := lintegral_mono fun x => le_self_add
  · calc c₂ * rhoLength ρ₂ μ₂ = ∫⁻ x, Ω₂.indicator (fun y => c₂ * ρ₂ y) x ∂μ₂ := by
          rw [lintegral_indicator_of_compl_null h₂, rhoLength, lintegral_const_mul c₂ hρ₂]
      _ ≤ rhoLength (gluedMetric Ω₁ Ω₂ c₁ c₂ ρ₁ ρ₂) μ₂ := lintegral_mono fun x => le_add_self

/-- On disjoint regions the squares of the two parts add up, so the area of the glued metric is
at most the sum of the weighted areas. -/
lemma rhoArea_gluedMetric_le (m : Measure α) (hΩ₁ : MeasurableSet Ω₁)
    (hdisj : Disjoint Ω₁ Ω₂) (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂) :
    rhoArea m (gluedMetric Ω₁ Ω₂ c₁ c₂ ρ₁ ρ₂) ≤
      c₁ ^ 2 * rhoArea m ρ₁ + c₂ ^ 2 * rhoArea m ρ₂ := by
  have key : ∀ x, gluedMetric Ω₁ Ω₂ c₁ c₂ ρ₁ ρ₂ x ^ 2 =
      Ω₁.indicator (fun y => c₁ ^ 2 * ρ₁ y ^ 2) x +
        Ω₂.indicator (fun y => c₂ ^ 2 * ρ₂ y ^ 2) x := by
    intro x
    by_cases hx₁ : x ∈ Ω₁
    · have hx₂ : x ∉ Ω₂ := Set.disjoint_left.1 hdisj hx₁
      simp [gluedMetric, hx₁, hx₂, mul_pow]
    · by_cases hx₂ : x ∈ Ω₂ <;> simp [gluedMetric, hx₁, hx₂, mul_pow]
  have hle : ∀ (Ω : Set α) (c : ℝ≥0∞) (ρ : α → ℝ≥0∞), Measurable ρ →
      ∫⁻ x, Ω.indicator (fun y => c ^ 2 * ρ y ^ 2) x ∂m ≤ c ^ 2 * rhoArea m ρ := by
    intro Ω c ρ hρ
    calc _ ≤ ∫⁻ x, c ^ 2 * ρ x ^ 2 ∂m := lintegral_mono fun x => Set.indicator_le_self _ _ x
      _ = c ^ 2 * rhoArea m ρ := lintegral_const_mul _ (hρ.pow_const 2)
  rw [rhoArea]
  simp only [key]
  rw [lintegral_add_left ((measurable_const.mul (hρ₁.pow_const 2)).indicator hΩ₁)]
  exact add_le_add (hle Ω₁ c₁ ρ₁ hρ₁) (hle Ω₂ c₂ ρ₂ hρ₂)

lemma sq_div_self_of_ne {r : ℝ≥0∞} (h0 : r ≠ 0) (htop : r ≠ ⊤) : r ^ 2 / r = r := by
  rw [sq]
  exact ENNReal.mul_div_cancel_right h0 htop

lemma sq_div_mul_le (ℓ A : ℝ≥0∞) : (ℓ / A) ^ 2 * A ≤ ℓ ^ 2 / A :=
  calc (ℓ / A) ^ 2 * A = ℓ ^ 2 / A * (A⁻¹ * A) := by simp only [div_eq_mul_inv]; ring
    _ ≤ ℓ ^ 2 / A * 1 := by gcongr; exact ENNReal.inv_mul_le_one A
    _ = ℓ ^ 2 / A := mul_one _

/-- The main case of the series law. Write `ℓᵢ` for the least `ρᵢ`-length of `Γᵢ` and `Aᵢ` for
the area of `ρᵢ`. The glued metric `(ℓ₁/A₁) ρ₁ 1_{Ω₁} + (ℓ₂/A₂) ρ₂ 1_{Ω₂}` has length at least
`ℓ₁²/A₁ + ℓ₂²/A₂` on every curve of `Γ` and area at most the same number, which is finite. -/
lemma series_main {m : Measure α} {Γ Γ₁ Γ₂ : Set (Measure α)} (hΩ₁ : MeasurableSet Ω₁)
    (hΩ₂ : MeasurableSet Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (h₁ : ∀ μ ∈ Γ₁, μ Ω₁ᶜ = 0) (h₂ : ∀ μ ∈ Γ₂, μ Ω₂ᶜ = 0)
    (h : ∀ μ ∈ Γ, ∃ μ₁ ∈ Γ₁, ∃ μ₂ ∈ Γ₂, μ₁ + μ₂ ≤ μ)
    (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (hfin : minLength ρ₁ Γ₁ ^ 2 / rhoArea m ρ₁ + minLength ρ₂ Γ₂ ^ 2 / rhoArea m ρ₂ ≠ ⊤) :
    minLength ρ₁ Γ₁ ^ 2 / rhoArea m ρ₁ + minLength ρ₂ Γ₂ ^ 2 / rhoArea m ρ₂ ≤
      extLength m Γ := by
  set ℓ₁ := minLength ρ₁ Γ₁
  set ℓ₂ := minLength ρ₂ Γ₂
  set A₁ := rhoArea m ρ₁
  set A₂ := rhoArea m ρ₂
  rcases eq_or_ne (ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂) 0 with h0 | h0
  · rw [h0]
    exact zero_le _
  set ρ := gluedMetric Ω₁ Ω₂ (ℓ₁ / A₁) (ℓ₂ / A₂) ρ₁ ρ₂
  have hlen : ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂ ≤ minLength ρ Γ := by
    refine le_minLength fun μ hμ => ?_
    obtain ⟨μ₁, hμ₁, μ₂, hμ₂, hle⟩ := h μ hμ
    calc ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂ = ℓ₁ / A₁ * ℓ₁ + ℓ₂ / A₂ * ℓ₂ := by
          simp only [div_eq_mul_inv]
          ring
      _ ≤ ℓ₁ / A₁ * rhoLength ρ₁ μ₁ + ℓ₂ / A₂ * rhoLength ρ₂ μ₂ := by
          gcongr
          · exact minLength_le_rhoLength hμ₁
          · exact minLength_le_rhoLength hμ₂
      _ ≤ rhoLength ρ (μ₁ + μ₂) := rhoLength_gluedMetric_ge hρ₁ hρ₂ (h₁ μ₁ hμ₁) (h₂ μ₂ hμ₂)
      _ ≤ rhoLength ρ μ := rhoLength_mono hle ρ
  have harea : rhoArea m ρ ≤ ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂ := by
    refine (rhoArea_gluedMetric_le m hΩ₁ hdisj hρ₁ hρ₂).trans ?_
    gcongr <;> exact sq_div_mul_le _ _
  calc ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂
      = (ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂) ^ 2 / (ℓ₁ ^ 2 / A₁ + ℓ₂ ^ 2 / A₂) :=
        (sq_div_self_of_ne h0 hfin).symm
    _ ≤ minLength ρ Γ ^ 2 / rhoArea m ρ := by gcongr
    _ ≤ extLength m Γ :=
        ratio_le_extLength (measurable_gluedMetric hΩ₁ hΩ₂ hρ₁ hρ₂) (harea.trans_lt hfin.lt_top)

end Series

/-- Series law (Grötzsch inequality): curves that split into a piece of `Γ₁` followed by a piece of
`Γ₂` living in disjoint regions have extremal length at least the sum. -/
theorem extLength_series {m : Measure α} {Γ Γ₁ Γ₂ : Set (Measure α)} {Ω₁ Ω₂ : Set α}
    (hΩ₁ : MeasurableSet Ω₁) (hΩ₂ : MeasurableSet Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (h₁ : ∀ μ ∈ Γ₁, μ Ω₁ᶜ = 0) (h₂ : ∀ μ ∈ Γ₂, μ Ω₂ᶜ = 0)
    (h : ∀ μ ∈ Γ, ∃ μ₁ ∈ Γ₁, ∃ μ₂ ∈ Γ₂, μ₁ + μ₂ ≤ μ) :
    extLength m Γ₁ + extLength m Γ₂ ≤ extLength m Γ := by
  have hle₁ : extLength m Γ₁ ≤ extLength m Γ := extLength_mono fun μ hμ => by
    obtain ⟨μ₁, hμ₁, μ₂, -, hle⟩ := h μ hμ
    exact ⟨μ₁, hμ₁, (Measure.le_add_right le_rfl).trans hle⟩
  have hle₂ : extLength m Γ₂ ≤ extLength m Γ := extLength_mono fun μ hμ => by
    obtain ⟨μ₁, -, μ₂, hμ₂, hle⟩ := h μ hμ
    exact ⟨μ₂, hμ₂, (Measure.le_add_left le_rfl).trans hle⟩
  refine extLength_add_le fun ρ₁ ρ₂ hρ₁ hA₁ hρ₂ hA₂ => ?_
  by_cases hfin : minLength ρ₁ Γ₁ ^ 2 / rhoArea m ρ₁ + minLength ρ₂ Γ₂ ^ 2 / rhoArea m ρ₂ = ⊤
  · have htop : extLength m Γ = ⊤ := by
      rcases ENNReal.add_eq_top.1 hfin with ht | ht
      · have := (ratio_le_extLength hρ₁ hA₁).trans hle₁
        rw [ht] at this
        exact top_le_iff.1 this
      · have := (ratio_le_extLength hρ₂ hA₂).trans hle₂
        rw [ht] at this
        exact top_le_iff.1 this
    rw [htop]
    exact le_top
  · exact series_main hΩ₁ hΩ₂ hdisj h₁ h₂ h hρ₁ hρ₂ hfin

section Parallel

lemma mul_inv_le_of_div_le {x a E : ℝ≥0∞} (h : x / a ≤ E) (ha : a ≠ ⊤) : x * E⁻¹ ≤ a := by
  rcases eq_or_ne E 0 with rfl | hE0
  · have hx : x = 0 := by
      rcases ENNReal.div_eq_zero_iff.1 (nonpos_iff_eq_zero.1 h) with hx | hx
      · exact hx
      · exact absurd hx ha
    simp [hx]
  rcases eq_or_ne E ⊤ with rfl | hEtop
  · simp
  have hx : x ≤ E * a := (ENNReal.div_le_iff_le_mul (Or.inr hEtop) (Or.inl ha)).1 h
  calc x * E⁻¹ ≤ E * a * E⁻¹ := by gcongr
    _ = a := by rw [mul_comm E a, mul_assoc, ENNReal.mul_inv_cancel hE0 hEtop, mul_one]

lemma div_le_inv_of_mul_le {x s A : ℝ≥0∞} (h : x * s ≤ A) (hA : A ≠ ⊤) : x / A ≤ s⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  rcases eq_or_ne s ⊤ with rfl | hstop
  · have hx : x = 0 := by
      by_contra hx
      rw [ENNReal.mul_top hx] at h
      exact hA (top_le_iff.1 h)
    simp [hx]
  refine ENNReal.div_le_of_le_mul ?_
  calc x = x * s * s⁻¹ := (ENNReal.mul_inv_cancel_right hs0 hstop).symm
    _ ≤ A * s⁻¹ := by gcongr
    _ = s⁻¹ * A := mul_comm _ _

lemma rhoArea_indicator_le (m : Measure α) (Ω : Set α) (ρ : α → ℝ≥0∞) :
    rhoArea m (Ω.indicator ρ) ≤ rhoArea m ρ :=
  lintegral_mono fun x => by
    gcongr
    exact Set.indicator_le_self Ω ρ x

/-- Restricting a metric to two disjoint regions splits its area. -/
lemma rhoArea_indicator_add_le (m : Measure α) {Ω₁ Ω₂ : Set α} (hΩ₁ : MeasurableSet Ω₁)
    (hdisj : Disjoint Ω₁ Ω₂) {ρ : α → ℝ≥0∞} (hρ : Measurable ρ) :
    rhoArea m (Ω₁.indicator ρ) + rhoArea m (Ω₂.indicator ρ) ≤ rhoArea m ρ := by
  have key : ∀ (Ω : Set α) x, Ω.indicator ρ x ^ 2 = Ω.indicator (fun y => ρ y ^ 2) x := by
    intro Ω x
    by_cases hx : x ∈ Ω <;> simp [hx]
  simp only [rhoArea, key]
  rw [← lintegral_add_left ((hρ.pow_const 2).indicator hΩ₁)]
  refine lintegral_mono fun x => ?_
  have h := congrFun (Set.indicator_union_of_disjoint hdisj fun y => ρ y ^ 2) x
  rw [← h]
  exact Set.indicator_le_self _ _ x

/-- If the curves of `Γ' ⊆ Γ` live in `Ω`, then `L² / λ' ≤ A'`, where `L` is the least `ρ`-length
of `Γ`, `λ'` the extremal length of `Γ'`, and `A'` the area of `ρ` restricted to `Ω`. -/
lemma piece_bound {m : Measure α} {Γ Γ' : Set (Measure α)} {Ω : Set α} (hΩ : MeasurableSet Ω)
    (hΓ' : ∀ μ ∈ Γ', μ Ωᶜ = 0) (hsub : Γ' ⊆ Γ) {ρ : α → ℝ≥0∞} (hρ : Measurable ρ)
    (hA : rhoArea m ρ < ⊤) :
    minLength ρ Γ ^ 2 * (extLength m Γ')⁻¹ ≤ rhoArea m (Ω.indicator ρ) := by
  have hA' : rhoArea m (Ω.indicator ρ) < ⊤ := (rhoArea_indicator_le m Ω ρ).trans_lt hA
  have hmin : minLength ρ Γ ≤ minLength (Ω.indicator ρ) Γ' := by
    refine (minLength_anti hsub).trans (le_minLength fun μ hμ => ?_)
    exact (minLength_le_rhoLength hμ).trans_eq (lintegral_indicator_of_compl_null (hΓ' μ hμ) ρ).symm
  have hratio := ratio_le_extLength (Γ := Γ') (hρ.indicator hΩ) hA'
  refine mul_inv_le_of_div_le (le_trans ?_ hratio) hA'.ne
  gcongr

end Parallel

/-- Parallel law: the widths of families in disjoint regions add up. -/
theorem extWidth_parallel {m : Measure α} {Γ₁ Γ₂ : Set (Measure α)} {Ω₁ Ω₂ : Set α}
    (hΩ₁ : MeasurableSet Ω₁) (hΩ₂ : MeasurableSet Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (h₁ : ∀ μ ∈ Γ₁, μ Ω₁ᶜ = 0) (h₂ : ∀ μ ∈ Γ₂, μ Ω₂ᶜ = 0) :
    extWidth m Γ₁ + extWidth m Γ₂ ≤ extWidth m (Γ₁ ∪ Γ₂) := by
  have key : extLength m (Γ₁ ∪ Γ₂) ≤ (extWidth m Γ₁ + extWidth m Γ₂)⁻¹ := by
    refine extLength_le fun ρ hρ hA => div_le_inv_of_mul_le ?_ hA.ne
    calc minLength ρ (Γ₁ ∪ Γ₂) ^ 2 * (extWidth m Γ₁ + extWidth m Γ₂)
        = minLength ρ (Γ₁ ∪ Γ₂) ^ 2 * (extLength m Γ₁)⁻¹ +
            minLength ρ (Γ₁ ∪ Γ₂) ^ 2 * (extLength m Γ₂)⁻¹ := mul_add _ _ _
      _ ≤ rhoArea m (Ω₁.indicator ρ) + rhoArea m (Ω₂.indicator ρ) :=
          add_le_add (piece_bound hΩ₁ h₁ Set.subset_union_left hρ hA)
            (piece_bound hΩ₂ h₂ Set.subset_union_right hρ hA)
      _ ≤ rhoArea m ρ := rhoArea_indicator_add_le m hΩ₁ hdisj hρ
  exact ENNReal.le_inv_iff_le_inv.2 key

/-- Estimate (4.6) of the survey, additive form: if the second piece already carries the fraction
`1 - δ` of the extremal length, the first piece has at most the fraction `δ`. -/
theorem extLength_complement_le {m : Measure α} {Γ Γ₁ Γ₂ : Set (Measure α)} {δ : ℝ≥0∞}
    (hδ : δ ≤ 1) (hser : extLength m Γ₁ + extLength m Γ₂ ≤ extLength m Γ)
    (hfin : extLength m Γ ≠ ⊤) (h₂ : (1 - δ) * extLength m Γ ≤ extLength m Γ₂) :
    extLength m Γ₁ ≤ δ * extLength m Γ := by
  have hfin' : (1 - δ) * extLength m Γ ≠ ⊤ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hfin
  refine (ENNReal.add_le_add_iff_right hfin').1 ?_
  calc extLength m Γ₁ + (1 - δ) * extLength m Γ ≤ extLength m Γ₁ + extLength m Γ₂ := by gcongr
    _ ≤ extLength m Γ := hser
    _ = (δ + (1 - δ)) * extLength m Γ := by rw [add_tsub_cancel_of_le hδ, one_mul]
    _ = δ * extLength m Γ + (1 - δ) * extLength m Γ := add_mul _ _ _

/-- Estimate (4.6) in widths: `W(Γ₁) ≥ δ⁻¹ W(Γ)`, the constant `C_δ = δ⁻¹ → ∞` as `δ → 0`. -/
theorem extWidth_ge_of_complement {m : Measure α} {Γ Γ₁ Γ₂ : Set (Measure α)} {δ : ℝ≥0∞}
    (hδ0 : δ ≠ 0) (hδ : δ ≤ 1) (hser : extLength m Γ₁ + extLength m Γ₂ ≤ extLength m Γ)
    (hfin : extLength m Γ ≠ ⊤) (h₂ : (1 - δ) * extLength m Γ ≤ extLength m Γ₂) :
    δ⁻¹ * extWidth m Γ ≤ extWidth m Γ₁ := by
  have h := extLength_complement_le hδ hser hfin h₂
  have hδtop : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hδ
  unfold extWidth
  rw [← ENNReal.mul_inv (Or.inl hδ0) (Or.inl hδtop)]
  exact ENNReal.inv_le_inv.2 h

/-- The Grötzsch estimate (4.6) from a series decomposition. A curve of `Γ` (the family of the
rectangle `G`) contains a curve of `Γ₁` (the subcurves `G ∖ G'` through the preperiodic Julia
sets, in the region `Ω₁`) followed by a curve of `Γ₂` (the lift `G'`, in the disjoint region
`Ω₂`). If `Γ₂` carries the fraction `1 - δ` of the extremal length of `Γ`, then
`W(G ∖ G') ≥ δ⁻¹ W(G)`, and `C_δ = δ⁻¹ → ∞` as `δ → 0`. -/
theorem extWidth_ge_of_series {m : Measure α} {Γ Γ₁ Γ₂ : Set (Measure α)} {Ω₁ Ω₂ : Set α}
    {δ : ℝ≥0∞} (hΩ₁ : MeasurableSet Ω₁) (hΩ₂ : MeasurableSet Ω₂) (hdisj : Disjoint Ω₁ Ω₂)
    (h₁ : ∀ μ ∈ Γ₁, μ Ω₁ᶜ = 0) (h₂ : ∀ μ ∈ Γ₂, μ Ω₂ᶜ = 0)
    (h : ∀ μ ∈ Γ, ∃ μ₁ ∈ Γ₁, ∃ μ₂ ∈ Γ₂, μ₁ + μ₂ ≤ μ)
    (hδ0 : δ ≠ 0) (hδ : δ ≤ 1) (hfin : extLength m Γ ≠ ⊤)
    (hlift : (1 - δ) * extLength m Γ ≤ extLength m Γ₂) :
    δ⁻¹ * extWidth m Γ ≤ extWidth m Γ₁ :=
  extWidth_ge_of_complement hδ0 hδ (extLength_series hΩ₁ hΩ₂ hdisj h₁ h₂ h) hfin hlift

section Pullback

variable {β : Type*} [MeasurableSpace β]

/-- Pullback: let `φ` carry the curves of `ΓX` to curves of `ΓY`, where a curve `μ` goes to
`(J μ).map φ`, and let the area elements satisfy `φ_*(J² mX) ≤ d · mY` (for a holomorphic map
of degree `d`, with `J = |φ'|`, the area formula gives the multiplicity of `φ`, which is at most
`d`). Then `λ(ΓY) ≤ d · λ(ΓX)`. -/
theorem extLength_pullback_le {mX : Measure α} {mY : Measure β} {ΓX : Set (Measure α)}
    {ΓY : Set (Measure β)} {φ : α → β} {J : α → ℝ≥0∞} {d : ℝ≥0∞} (hφ : Measurable φ)
    (hJ : Measurable J) (hd0 : d ≠ 0) (hdtop : d ≠ ⊤)
    (harea : (mX.withDensity fun x => J x ^ 2).map φ ≤ d • mY)
    (hcurve : ∀ μ ∈ ΓX, (μ.withDensity J).map φ ∈ ΓY) :
    extLength mY ΓY ≤ d * extLength mX ΓX := by
  refine extLength_le fun ρ hρ hA => ?_
  have hρφ : Measurable fun x => ρ (φ x) := hρ.comp hφ
  have hρ' : Measurable fun x => J x * ρ (φ x) := hJ.mul hρφ
  have hlen : minLength ρ ΓY ≤ minLength (fun x => J x * ρ (φ x)) ΓX := by
    refine le_minLength fun μ hμ => ?_
    have h1 : rhoLength (fun x => J x * ρ (φ x)) μ = rhoLength ρ ((μ.withDensity J).map φ) := by
      unfold rhoLength
      rw [lintegral_map hρ hφ, lintegral_withDensity_eq_lintegral_mul _ hJ hρφ]
      rfl
    rw [h1]
    exact minLength_le_rhoLength (hcurve μ hμ)
  have harea' : rhoArea mX (fun x => J x * ρ (φ x)) ≤ d * rhoArea mY ρ := by
    have h1 : rhoArea mX (fun x => J x * ρ (φ x)) =
        ∫⁻ x, ρ (φ x) ^ 2 ∂(mX.withDensity fun x => J x ^ 2) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ (hJ.pow_const 2) (hρφ.pow_const 2)]
      refine lintegral_congr fun x => ?_
      simp [mul_pow]
    rw [h1, ← lintegral_map (hρ.pow_const 2) hφ]
    calc ∫⁻ y, ρ y ^ 2 ∂(mX.withDensity fun x => J x ^ 2).map φ ≤ ∫⁻ y, ρ y ^ 2 ∂(d • mY) :=
          lintegral_mono' harea le_rfl
      _ = d * rhoArea mY ρ := by rw [lintegral_smul_measure]; rfl
  have hA' : rhoArea mX (fun x => J x * ρ (φ x)) < ⊤ :=
    harea'.trans_lt (ENNReal.mul_lt_top hdtop.lt_top hA)
  have hratio := ratio_le_extLength (m := mX) (Γ := ΓX) hρ' hA'
  set ℓ := minLength ρ ΓY
  set ℓ' := minLength (fun x => J x * ρ (φ x)) ΓX
  set A := rhoArea mY ρ
  set A' := rhoArea mX (fun x => J x * ρ (φ x))
  calc ℓ ^ 2 / A ≤ ℓ' ^ 2 / A := by gcongr
    _ = d * (ℓ' ^ 2 / (d * A)) := by
        rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hd0 hdtop]
    _ ≤ d * (ℓ' ^ 2 / A') := by gcongr
    _ ≤ d * extLength mX ΓX := by gcongr

/-- Pullback in widths: `W(ΓX) ≤ d · W(ΓY)`. For `φ` a map of degree `d` this is the estimate
behind the Teichmüller contraction: the width of a pulled-back family exceeds the width of the
family by at most the degree, and for `d = 1` it is conformal invariance. -/
theorem extWidth_pullback_le {mX : Measure α} {mY : Measure β} {ΓX : Set (Measure α)}
    {ΓY : Set (Measure β)} {φ : α → β} {J : α → ℝ≥0∞} {d : ℝ≥0∞} (hφ : Measurable φ)
    (hJ : Measurable J) (hd0 : d ≠ 0) (hdtop : d ≠ ⊤)
    (harea : (mX.withDensity fun x => J x ^ 2).map φ ≤ d • mY)
    (hcurve : ∀ μ ∈ ΓX, (μ.withDensity J).map φ ∈ ΓY) :
    extWidth mX ΓX ≤ d * extWidth mY ΓY := by
  have h := extLength_pullback_le hφ hJ hd0 hdtop harea hcurve
  have h2 : (d * extLength mX ΓX)⁻¹ ≤ (extLength mY ΓY)⁻¹ := ENNReal.inv_le_inv.2 h
  rw [ENNReal.mul_inv (Or.inl hd0) (Or.inl hdtop)] at h2
  unfold extWidth
  calc (extLength mX ΓX)⁻¹ = d * (d⁻¹ * (extLength mX ΓX)⁻¹) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hd0 hdtop, one_mul]
    _ ≤ d * (extLength mY ΓY)⁻¹ := by gcongr

end Pullback

/-- The parallel law for finitely many families: if the families `Γ i` live in pairwise disjoint
regions `Ω i`, the width of their union is at least the sum of the widths. With `p` small Julia
sets of equal degeneration `W(f₁)` in disjoint neighbourhoods, the total degeneration around
them is at least `p W(f₁)`, the term `p W(f₁)` of (4.1). -/
theorem extWidth_parallel_finset {ι : Type*} {m : Measure α} (s : Finset ι)
    {Γ : ι → Set (Measure α)} {Ω : ι → Set α} (hΩ : ∀ i ∈ s, MeasurableSet (Ω i))
    (hdisj : (s : Set ι).PairwiseDisjoint Ω) (h : ∀ i ∈ s, ∀ μ ∈ Γ i, μ (Ω i)ᶜ = 0) :
    ∑ i ∈ s, extWidth m (Γ i) ≤ extWidth m (⋃ i ∈ s, Γ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hΩ' : MeasurableSet (⋃ i ∈ s, Ω i) :=
      Finset.measurableSet_biUnion s fun i hi => hΩ i (hs i hi)
    have hdisj' : Disjoint (Ω a) (⋃ i ∈ s, Ω i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hdisj (Finset.mem_insert_self a s) (Finset.mem_coe.2 (hs i hi))
        (fun hai => ha (hai ▸ hi))
    have hΓ' : ∀ μ ∈ ⋃ i ∈ s, Γ i, μ (⋃ i ∈ s, Ω i)ᶜ = 0 := by
      intro μ hμ
      obtain ⟨i, hi, hμi⟩ := Set.mem_iUnion₂.1 hμ
      exact measure_mono_null (Set.compl_subset_compl.2 (Set.subset_iUnion₂ i hi))
        (h i (hs i hi) μ hμi)
    have key := extWidth_parallel (m := m) (hΩ a (Finset.mem_insert_self a s)) hΩ' hdisj'
      (h a (Finset.mem_insert_self a s)) hΓ'
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    refine le_trans ?_ key
    gcongr
    exact ih (fun i hi => hΩ i (hs i hi))
      (hdisj.subset (Finset.coe_subset.2 (Finset.subset_insert a s))) (fun i hi => h i (hs i hi))

end

end MLC.Research
