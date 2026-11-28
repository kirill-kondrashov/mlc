import Mlc.Research.AnnulusModulus

/-!
# The modulus of a rectangle

The survey of Dudko measures the degeneration of a level by extremal widths of rectangles
(the combinatorially invariant rectangles `G ⊃ G′` of Figure 13, and the estimate (4.6)). This
module computes the extremal length of the model rectangle `(x₀, x₁] × (y₀, y₁]` of the plane
with Lebesgue measure, in the coordinates `z = x + i y`: the family of the horizontal segments,
which join its vertical sides, has extremal length `(x₁ - x₀) / (y₁ - y₀)`
(`extLength_horizFamily`), and the extremal width is the reciprocal `(y₁ - y₀) / (x₁ - x₀)`
(`extWidth_horizFamily`). The proof is the Cauchy–Schwarz inequality along a segment and Fubini
for the upper bound, and the characteristic function of the rectangle for the lower bound.
Together with `Mlc/Research/AnnulusModulus.lean`, the abstract extremal length of
`Mlc/Research/ExtremalLength.lean` agrees with the classical modulus on both model domains.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real

noncomputable section

/-- The point `x + i y` of the plane. -/
def rc (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

lemma measurable_rc : Measurable rc :=
  Complex.measurableEquivRealProd.symm.measurable

lemma measurable_rc_left (y : ℝ) : Measurable fun x : ℝ => rc (x, y) :=
  measurable_rc.comp (measurable_id.prodMk measurable_const)

/-- Lebesgue measure of the plane in the coordinates `x`, `y`. -/
lemma lintegral_rc (g : ℂ → ℝ≥0∞) : ∫⁻ p : ℝ × ℝ, g (rc p) = ∫⁻ z, g z :=
  (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding g

/-- The length measure of the horizontal segment `x + i y`, `x₀ < x ≤ x₁`. -/
def horizCurve (x₀ x₁ y : ℝ) : Measure ℂ :=
  (volume.restrict (Ioc x₀ x₁)).map fun x : ℝ => rc (x, y)

/-- The horizontal segments of the rectangle `(x₀, x₁] × (y₀, y₁]`: the curves that join its
vertical sides. -/
def horizFamily (x₀ x₁ y₀ y₁ : ℝ) : Set (Measure ℂ) := horizCurve x₀ x₁ '' Ioc y₀ y₁

lemma rhoLength_horizCurve {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (x₀ x₁ y : ℝ) :
    rhoLength ρ (horizCurve x₀ x₁ y) = ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) := by
  unfold rhoLength horizCurve
  exact lintegral_map hρ (measurable_rc_left y)

/-- **Upper bound for the horizontal family.** -/
theorem ratio_horizFamily_le {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) :
    minLength ρ (horizFamily x₀ x₁ y₀ y₁) ^ 2 / rhoArea volume ρ ≤
      ENNReal.ofReal ((x₁ - x₀) / (y₁ - y₀)) := by
  set L := minLength ρ (horizFamily x₀ x₁ y₀ y₁) with hL
  set A := rhoArea volume ρ with hA
  have hw : 0 < x₁ - x₀ := sub_pos.2 hx
  have hh : 0 < y₁ - y₀ := sub_pos.2 hy
  have hρ1 : ∀ y : ℝ, Measurable fun x : ℝ => ρ (rc (x, y)) := fun y =>
    hρ.comp (measurable_rc_left y)
  have hy' : ∀ y ∈ Ioc y₀ y₁, L ^ 2 ≤
      ENNReal.ofReal (x₁ - x₀) * ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) ^ 2 := by
    intro y hy
    have hLle : L ≤ ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) := by
      rw [← rhoLength_horizCurve hρ]
      exact minLength_le_rhoLength ⟨y, hy, rfl⟩
    have hcs := lintegral_mul_sq_le (volume.restrict (Ioc x₀ x₁)) (f := fun x => ρ (rc (x, y)))
      (g := fun _ => 1) (hρ1 y).aemeasurable aemeasurable_const
    simp only [mul_one, one_pow, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Ioc, one_mul] at hcs
    calc L ^ 2 ≤ (∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y))) ^ 2 := by gcongr
      _ ≤ _ := by rw [mul_comm]; exact hcs
  have hF : Measurable fun p : ℝ × ℝ => ρ (rc p) ^ 2 := (hρ.comp measurable_rc).pow_const 2
  have hfub : ∫⁻ y in Ioc y₀ y₁, ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) ^ 2 ≤ A := by
    calc ∫⁻ y in Ioc y₀ y₁, ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) ^ 2
        = ∫⁻ p in Ioc x₀ x₁ ×ˢ Ioc y₀ y₁, ρ (rc p) ^ 2 := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
          exact (lintegral_prod_symm (fun p : ℝ × ℝ => ρ (rc p) ^ 2) hF.aemeasurable).symm
      _ ≤ ∫⁻ p : ℝ × ℝ, ρ (rc p) ^ 2 := setLIntegral_le_lintegral _ _
      _ = A := lintegral_rc fun z => ρ z ^ 2
  have hint : ENNReal.ofReal (y₁ - y₀) * L ^ 2 ≤ ENNReal.ofReal (x₁ - x₀) * A := by
    calc ENNReal.ofReal (y₁ - y₀) * L ^ 2 = ∫⁻ _ in Ioc y₀ y₁, L ^ 2 := by
          rw [setLIntegral_const, Real.volume_Ioc, mul_comm]
      _ ≤ ∫⁻ y in Ioc y₀ y₁, ENNReal.ofReal (x₁ - x₀) * ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) ^ 2 :=
          setLIntegral_mono' measurableSet_Ioc hy'
      _ = ENNReal.ofReal (x₁ - x₀) * ∫⁻ y in Ioc y₀ y₁, ∫⁻ x in Ioc x₀ x₁, ρ (rc (x, y)) ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (x₁ - x₀) * A := by gcongr
  have hh0 : ENNReal.ofReal (y₁ - y₀) ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  rcases eq_or_ne A 0 with h0 | h0
  · rw [h0, mul_zero, nonpos_iff_eq_zero] at hint
    have : L ^ 2 = 0 := (mul_eq_zero.1 hint).resolve_left hh0
    rw [this, h0]
    simp
  rcases eq_or_ne A ⊤ with htop | htop
  · rw [htop]
    simp
  rw [ENNReal.div_le_iff h0 htop]
  refine (ENNReal.mul_le_mul_iff_right hh0 ENNReal.ofReal_ne_top).1 ?_
  calc ENNReal.ofReal (y₁ - y₀) * L ^ 2 ≤ ENNReal.ofReal (x₁ - x₀) * A := hint
    _ = ENNReal.ofReal (y₁ - y₀) * (ENNReal.ofReal ((x₁ - x₀) / (y₁ - y₀)) * A) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, mul_div_cancel₀ _ hh.ne']

/-- The characteristic function of the rectangle `(x₀, x₁] × (y₀, y₁]`. -/
def rectMetric (x₀ x₁ y₀ y₁ : ℝ) (z : ℂ) : ℝ≥0∞ :=
  if z.re ∈ Ioc x₀ x₁ ∧ z.im ∈ Ioc y₀ y₁ then 1 else 0

lemma measurable_rectMetric (x₀ x₁ y₀ y₁ : ℝ) : Measurable (rectMetric x₀ x₁ y₀ y₁) := by
  unfold rectMetric
  exact Measurable.ite
    ((measurableSet_Ioc.preimage Complex.measurable_re).inter
      (measurableSet_Ioc.preimage Complex.measurable_im)) measurable_const measurable_const

/-- Every horizontal segment has length `x₁ - x₀` for the characteristic function. -/
lemma rhoLength_rectMetric {x₀ x₁ y₀ y₁ y : ℝ} (hy : y ∈ Ioc y₀ y₁) :
    rhoLength (rectMetric x₀ x₁ y₀ y₁) (horizCurve x₀ x₁ y) = ENNReal.ofReal (x₁ - x₀) := by
  rw [rhoLength_horizCurve (measurable_rectMetric x₀ x₁ y₀ y₁)]
  have : ∀ x ∈ Ioc x₀ x₁, rectMetric x₀ x₁ y₀ y₁ (rc (x, y)) = 1 := fun x hx => by
    simp [rectMetric, rc, hx, hy]
  rw [setLIntegral_congr_fun measurableSet_Ioc this]
  simp [Real.volume_Ioc]

/-- The characteristic function of the rectangle has area `(x₁ - x₀) (y₁ - y₀)`. -/
lemma rhoArea_rectMetric (x₀ x₁ y₀ y₁ : ℝ) :
    rhoArea volume (rectMetric x₀ x₁ y₀ y₁) =
      ENNReal.ofReal (x₁ - x₀) * ENNReal.ofReal (y₁ - y₀) := by
  have hsq : ∀ p : ℝ × ℝ, rectMetric x₀ x₁ y₀ y₁ (rc p) ^ 2 =
      (Ioc x₀ x₁ ×ˢ Ioc y₀ y₁).indicator 1 p := by
    intro p
    by_cases h : p ∈ Ioc x₀ x₁ ×ˢ Ioc y₀ y₁
    · simp only [Set.indicator_of_mem h]
      have h' : (rc p).re ∈ Ioc x₀ x₁ ∧ (rc p).im ∈ Ioc y₀ y₁ := h
      rw [show rectMetric x₀ x₁ y₀ y₁ (rc p) = 1 from if_pos h']
      simp
    · simp only [Set.indicator_of_notMem h]
      have h' : ¬((rc p).re ∈ Ioc x₀ x₁ ∧ (rc p).im ∈ Ioc y₀ y₁) := h
      rw [show rectMetric x₀ x₁ y₀ y₁ (rc p) = 0 from if_neg h']
      simp
  unfold rhoArea
  rw [← lintegral_rc fun z => rectMetric x₀ x₁ y₀ y₁ z ^ 2]
  simp only [hsq]
  rw [lintegral_indicator_one (measurableSet_Ioc.prod measurableSet_Ioc), Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]

/-- **Lower bound for the horizontal family.** -/
theorem ofReal_le_extLength_horizFamily {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) :
    ENNReal.ofReal ((x₁ - x₀) / (y₁ - y₀)) ≤ extLength volume (horizFamily x₀ x₁ y₀ y₁) := by
  have hw : 0 < x₁ - x₀ := sub_pos.2 hx
  have hh : 0 < y₁ - y₀ := sub_pos.2 hy
  have harea := rhoArea_rectMetric x₀ x₁ y₀ y₁
  refine le_trans ?_ (ratio_le_extLength (measurable_rectMetric x₀ x₁ y₀ y₁) ?_)
  · have hmin : ENNReal.ofReal (x₁ - x₀) ≤
        minLength (rectMetric x₀ x₁ y₀ y₁) (horizFamily x₀ x₁ y₀ y₁) :=
      le_minLength fun μ hμ => by
        obtain ⟨y, hy', rfl⟩ := hμ
        exact (rhoLength_rectMetric hy').ge
    rw [harea]
    calc ENNReal.ofReal ((x₁ - x₀) / (y₁ - y₀))
        = ENNReal.ofReal (x₁ - x₀) ^ 2 /
            (ENNReal.ofReal (x₁ - x₀) * ENNReal.ofReal (y₁ - y₀)) := by
          rw [← ENNReal.ofReal_mul hw.le, ← ENNReal.ofReal_pow hw.le,
            ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          field_simp
      _ ≤ minLength (rectMetric x₀ x₁ y₀ y₁) (horizFamily x₀ x₁ y₀ y₁) ^ 2 /
            (ENNReal.ofReal (x₁ - x₀) * ENNReal.ofReal (y₁ - y₀)) := by gcongr
  · rw [harea]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The modulus of a rectangle**: the extremal length of the family of the horizontal segments
of `(x₀, x₁] × (y₀, y₁]`, which join its vertical sides, is `(x₁ - x₀) / (y₁ - y₀)`. -/
theorem extLength_horizFamily {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) :
    extLength volume (horizFamily x₀ x₁ y₀ y₁) = ENNReal.ofReal ((x₁ - x₀) / (y₁ - y₀)) :=
  le_antisymm (extLength_le fun _ hρ _ => ratio_horizFamily_le hx hy hρ)
    (ofReal_le_extLength_horizFamily hx hy)

/-- The extremal width of the horizontal segments of a rectangle is the ratio of its height to its
width. -/
theorem extWidth_horizFamily {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁) :
    extWidth volume (horizFamily x₀ x₁ y₀ y₁) = ENNReal.ofReal ((y₁ - y₀) / (x₁ - x₀)) := by
  have hw : 0 < x₁ - x₀ := sub_pos.2 hx
  have hh : 0 < y₁ - y₀ := sub_pos.2 hy
  rw [extWidth, extLength_horizFamily hx hy, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

end

end MLC.Research
