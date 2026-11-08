import Yoccoz.Quadratic.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Compactness.Compact

/-!
# First hyperbolic components: multipliers, the cardioid, and the period-two disk

For the quadratic family `f_c(z) = z^2 + c` this file proves the component
formulas used in Chapter 13 of the review:

* the chain-rule product for the multiplier of an iterate;
* the main cardioid `H₀ = {c | f_c has an attracting fixed point}` is the image of
  the open unit disk under `t ↦ t/2 - t^2/4`; this parametrization is injective on
  the closed disk, the attracting fixed point is unique, and the frontier of `H₀`
  is the image of the unit circle;
* the period-two component `H₂ = {c | f_c has an attracting cycle of prime period
  two}` is the disk `|c + 1| < 1/4`, with cycle multiplier `4(c + 1)`.

Nothing here identifies these sets with components of the interior of the
Mandelbrot set, and nothing here treats other periods.
-/

namespace MLC.Quadratic.FirstComponents

open Complex Metric Set Filter Topology

noncomputable section

/-! ### Multipliers of iterates -/

lemma hasDerivAt_fc (c z : ℂ) : HasDerivAt (fc c) (2 * z) z := by
  have h := (hasDerivAt_pow 2 z).add_const c
  have hfun : fc c = fun x : ℂ => x ^ 2 + c := rfl
  rw [hfun]
  convert h using 1
  norm_num

lemma hasDerivAt_fc_iterate (c z : ℂ) (p : ℕ) :
    HasDerivAt ((fc c)^[p]) (∏ j ∈ Finset.range p, 2 * (fc c)^[j] z) z := by
  induction p with
  | zero => simpa using hasDerivAt_id z
  | succ p ih =>
    rw [Function.iterate_succ', Finset.prod_range_succ]
    convert (hasDerivAt_fc c ((fc c)^[p] z)).comp z ih using 1
    ring

theorem deriv_fc_iterate (c z : ℂ) (p : ℕ) :
    deriv ((fc c)^[p]) z = ∏ j ∈ Finset.range p, 2 * (fc c)^[j] z :=
  (hasDerivAt_fc_iterate c z p).deriv

theorem deriv_fc (c z : ℂ) : deriv (fc c) z = 2 * z :=
  (hasDerivAt_fc c z).deriv

theorem deriv_fc_two (c z : ℂ) : deriv ((fc c)^[2]) z = 2 * z * (2 * fc c z) := by
  rw [deriv_fc_iterate]
  simp [Finset.prod_range_succ]

/-! ### Period-two points -/

theorem period_two_factorization (c z : ℂ) :
    fc c (fc c z) - z = (z ^ 2 - z + c) * (z ^ 2 + z + c + 1) := by
  simp only [fc]
  ring

/-- For a non-fixed point of period two, `z · f_c(z) = c + 1`. -/
theorem period_two_mul {c z : ℂ} (hz : fc c (fc c z) = z) (hne : fc c z ≠ z) :
    z * fc c z = c + 1 := by
  have hfac := period_two_factorization c z
  rw [hz, sub_self] at hfac
  have hfix : z ^ 2 - z + c ≠ 0 := fun h => hne (by
    show z ^ 2 + c = z
    linear_combination h)
  have hcycle : z ^ 2 + z + c + 1 = 0 :=
    (mul_eq_zero.mp hfac.symm).resolve_left hfix
  show z * (z ^ 2 + c) = c + 1
  linear_combination (z - 1) * hcycle

/-- The cycle multiplier of a non-fixed period-two point is `4(c + 1)`. -/
theorem period_two_multiplier {c z : ℂ} (hz : fc c (fc c z) = z) (hne : fc c z ≠ z) :
    deriv ((fc c)^[2]) z = 4 * (c + 1) := by
  rw [deriv_fc_two]
  linear_combination 4 * period_two_mul hz hne

/-! ### The main cardioid -/

/-- The parametrization `t ↦ t/2 - t²/4` of the main cardioid. -/
def cardioidMap (t : ℂ) : ℂ := t / 2 - t ^ 2 / 4

theorem cardioidMap_differentiable : Differentiable ℂ cardioidMap := by
  unfold cardioidMap
  fun_prop

theorem cardioidMap_continuous : Continuous cardioidMap :=
  cardioidMap_differentiable.continuous

/-- `f_c` has an attracting fixed point: a fixed point whose multiplier has modulus below `1`. -/
def HasAttractingFixedPoint (c : ℂ) : Prop :=
  ∃ z : ℂ, fc c z = z ∧ ‖deriv (fc c) z‖ < 1

theorem hasAttractingFixedPoint_iff_mem_image (c : ℂ) :
    HasAttractingFixedPoint c ↔ c ∈ cardioidMap '' ball (0 : ℂ) 1 := by
  constructor
  · rintro ⟨z, hz, hnorm⟩
    have hfix : z ^ 2 + c = z := hz
    rw [deriv_fc] at hnorm
    refine ⟨2 * z, mem_ball_zero_iff.mpr hnorm, ?_⟩
    unfold cardioidMap
    linear_combination (-1 : ℂ) * hfix
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / 2, ?_, ?_⟩
    · show (t / 2) ^ 2 + cardioidMap t = t / 2
      unfold cardioidMap
      ring
    · rw [deriv_fc, show 2 * (t / 2) = t by ring]
      exact mem_ball_zero_iff.mp ht

theorem cardioidMap_injOn_closedBall : InjOn cardioidMap (closedBall (0 : ℂ) 1) := by
  intro t ht s hs hts
  have ht1 : ‖t‖ ≤ 1 := mem_closedBall_zero_iff.mp ht
  have hs1 : ‖s‖ ≤ 1 := mem_closedBall_zero_iff.mp hs
  unfold cardioidMap at hts
  have key : (t - s) * (2 - (t + s)) = 0 := by
    linear_combination 4 * hts
  rcases mul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · have hsum : t + s = 2 := by linear_combination (-1 : ℂ) * h
    have hs' : s = 2 - t := by linear_combination hsum
    rw [hs'] at hs1
    have hsq1 : ‖t‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg t]
    have hsq2 : ‖2 - t‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (2 - t)]
    rw [Complex.sq_norm, Complex.normSq_apply] at hsq1 hsq2
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat] at hsq2
    have hre : t.re = 1 := by nlinarith [sq_nonneg t.im]
    have him : t.im = 0 := by nlinarith [sq_nonneg t.im]
    have ht_one : t = 1 := Complex.ext (by simpa using hre) (by simpa using him)
    rw [hs', ht_one]
    norm_num

theorem isOpen_image_ball_cardioid : IsOpen (cardioidMap '' ball (0 : ℂ) 1) := by
  have hana : AnalyticOnNhd ℂ cardioidMap (ball (0 : ℂ) 1) :=
    fun z _ => cardioidMap_differentiable.analyticAt z
  rcases hana.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with
    ⟨w, hw⟩ | hopen
  · exfalso
    have h0 : cardioidMap 0 = w := hw 0 (mem_ball_self one_pos)
    have hhalf : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      norm_num [norm_div]
    have h1 : cardioidMap (1 / 2) = w := hw _ hhalf
    have heq : cardioidMap (1 / 2) = cardioidMap 0 := by rw [h0, h1]
    unfold cardioidMap at heq
    norm_num at heq
  · exact hopen _ subset_rfl isOpen_ball

theorem closure_image_ball_cardioid :
    closure (cardioidMap '' ball (0 : ℂ) 1) = cardioidMap '' closedBall (0 : ℂ) 1 := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall _ _).image cardioidMap_continuous).isClosed
  · rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact image_closure_subset_closure_image cardioidMap_continuous

theorem frontier_hasAttractingFixedPoint :
    frontier {c : ℂ | HasAttractingFixedPoint c} = cardioidMap '' sphere (0 : ℂ) 1 := by
  have hset : {c : ℂ | HasAttractingFixedPoint c} = cardioidMap '' ball (0 : ℂ) 1 :=
    Set.ext fun c => hasAttractingFixedPoint_iff_mem_image c
  rw [hset, frontier, closure_image_ball_cardioid, isOpen_image_ball_cardioid.interior_eq]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hnot⟩
    refine ⟨t, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    refine le_antisymm (mem_closedBall_zero_iff.mp ht) ?_
    by_contra hlt
    push_neg at hlt
    exact hnot ⟨t, mem_ball_zero_iff.mpr hlt, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, sphere_subset_closedBall ht, rfl⟩, ?_⟩
    rintro ⟨s, hs, hst⟩
    have hst' : s = t :=
      cardioidMap_injOn_closedBall (ball_subset_closedBall hs) (sphere_subset_closedBall ht) hst
    have hnt : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
    have hns : ‖s‖ < 1 := mem_ball_zero_iff.mp hs
    rw [hst'] at hns
    linarith

/-- Two attracting fixed points of `f_c` coincide, so the multiplier map is well defined. -/
theorem attracting_fixed_point_unique {c z w : ℂ} (hz : fc c z = z) (hw : fc c w = w)
    (hzn : ‖2 * z‖ < 1) (hwn : ‖2 * w‖ < 1) : z = w := by
  have hz' : z ^ 2 + c = z := hz
  have hw' : w ^ 2 + c = w := hw
  have hfix : (z - w) * (z + w - 1) = 0 := by
    linear_combination hz' - hw'
  rcases mul_eq_zero.mp hfix with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hsum : 2 * z + 2 * w = 2 := by linear_combination 2 * h
    have htri : ‖(2 : ℂ)‖ ≤ ‖2 * z‖ + ‖2 * w‖ := by
      calc ‖(2 : ℂ)‖ = ‖2 * z + 2 * w‖ := by rw [hsum]
        _ ≤ ‖2 * z‖ + ‖2 * w‖ := norm_add_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith

/-! ### The attracting period-two component -/

/-- `f_c` has an attracting cycle of prime period two. -/
def HasAttractingPeriodTwoCycle (c : ℂ) : Prop :=
  ∃ z : ℂ, (fc c)^[2] z = z ∧ fc c z ≠ z ∧ ‖deriv ((fc c)^[2]) z‖ < 1

theorem hasAttractingPeriodTwoCycle_iff (c : ℂ) :
    HasAttractingPeriodTwoCycle c ↔ c ∈ ball (-1 : ℂ) (1 / 4) := by
  rw [mem_ball, dist_eq_norm, sub_neg_eq_add]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  constructor
  · rintro ⟨z, hz, hne, hnorm⟩
    rw [period_two_multiplier hz hne, norm_mul, h4] at hnorm
    linarith
  · intro hc
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * (c + 1)) (by norm_num : 0 < 2)
    obtain ⟨z, hzs⟩ : ∃ z : ℂ, 2 * z = -1 + s := ⟨(-1 + s) / 2, by ring⟩
    have hcycle : z ^ 2 + z + c + 1 = 0 := by
      linear_combination ((2 * z + 1 + s) / 4) * hzs + (1 / 4 : ℂ) * hs
    have hz2 : (fc c)^[2] z = z := by
      have hfac := period_two_factorization c z
      rw [hcycle, mul_zero, sub_eq_zero] at hfac
      exact hfac
    have hne : fc c z ≠ z := by
      intro h
      have hfix : z ^ 2 + c = z := h
      have hzval : z = -1 / 2 := by linear_combination (hcycle - hfix) / 2
      have hc4 : c = -3 / 4 := by
        rw [hzval] at hcycle
        linear_combination hcycle
      rw [hc4] at hc
      norm_num [norm_div] at hc
    refine ⟨z, hz2, hne, ?_⟩
    rw [period_two_multiplier hz2 hne, norm_mul, h4]
    linarith

theorem frontier_hasAttractingPeriodTwoCycle :
    frontier {c : ℂ | HasAttractingPeriodTwoCycle c} = sphere (-1 : ℂ) (1 / 4) := by
  have hset : {c : ℂ | HasAttractingPeriodTwoCycle c} = ball (-1 : ℂ) (1 / 4) :=
    Set.ext fun c => hasAttractingPeriodTwoCycle_iff c
  rw [hset, frontier_ball (-1 : ℂ) (by norm_num : (1 / 4 : ℝ) ≠ 0)]

/-- The period-one and period-two components are disjoint. -/
theorem disjoint_cardioid_period_two :
    Disjoint {c : ℂ | HasAttractingFixedPoint c} {c : ℂ | HasAttractingPeriodTwoCycle c} := by
  rw [Set.disjoint_left]
  intro c hc0 hc2
  obtain ⟨t, ht, rfl⟩ := (hasAttractingFixedPoint_iff_mem_image _).mp hc0
  have hb := (hasAttractingPeriodTwoCycle_iff _).mp hc2
  rw [mem_ball, dist_eq_norm, sub_neg_eq_add] at hb
  have hid : (5 : ℂ) - (t - 1) ^ 2 = 4 * (cardioidMap t + 1) := by
    unfold cardioidMap
    ring
  have hlt : ‖(5 : ℂ) - (t - 1) ^ 2‖ < 1 := by
    rw [hid, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    linarith
  have hnorm := norm_sub_norm_le (5 : ℂ) ((t - 1) ^ 2)
  rw [norm_pow, show ‖(5 : ℂ)‖ = 5 by norm_num] at hnorm
  have ht1 : ‖t - 1‖ < 2 := by
    have h := norm_sub_le t 1
    rw [norm_one] at h
    have h' := mem_ball_zero_iff.mp ht
    linarith
  nlinarith [norm_nonneg (t - 1)]

/-- The closures of the two components meet only at the root `c = -3/4` of the bulb. -/
theorem closure_cardioid_inter_closure_period_two :
    closure {c : ℂ | HasAttractingFixedPoint c} ∩
        closure {c : ℂ | HasAttractingPeriodTwoCycle c} = {(-3 / 4 : ℂ)} := by
  have hset0 : {c : ℂ | HasAttractingFixedPoint c} = cardioidMap '' ball (0 : ℂ) 1 :=
    Set.ext fun c => hasAttractingFixedPoint_iff_mem_image c
  have hset2 : {c : ℂ | HasAttractingPeriodTwoCycle c} = ball (-1 : ℂ) (1 / 4) :=
    Set.ext fun c => hasAttractingPeriodTwoCycle_iff c
  rw [hset0, hset2, closure_image_ball_cardioid,
    closure_ball (-1 : ℂ) (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  ext c
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hc
    have ht1 : ‖t‖ ≤ 1 := mem_closedBall_zero_iff.mp ht
    have hid : (5 : ℂ) - (t - 1) ^ 2 = 4 * (cardioidMap t + 1) := by
      unfold cardioidMap
      ring
    have hle : ‖(5 : ℂ) - (t - 1) ^ 2‖ ≤ 1 := by
      rw [hid, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
      linarith
    have hnorm := norm_sub_norm_le (5 : ℂ) ((t - 1) ^ 2)
    rw [norm_pow, show ‖(5 : ℂ)‖ = 5 by norm_num] at hnorm
    have hge : 2 ≤ ‖t - 1‖ := by nlinarith [norm_nonneg (t - 1)]
    have hsq1 : ‖t‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg t]
    have hsq2 : 4 ≤ ‖t - 1‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm, Complex.normSq_apply] at hsq1 hsq2
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      sub_zero] at hsq2
    have hx : t.re = -1 := by
      nlinarith [sq_nonneg t.im, sq_nonneg (t.re + 1), sq_nonneg (t.re - 1)]
    have hy2 : t.im * t.im = 0 :=
      le_antisymm (by rw [hx] at hsq1; nlinarith) (mul_self_nonneg _)
    have hy : t.im = 0 := mul_self_eq_zero.mp hy2
    have ht_eq : t = -1 := Complex.ext (by simpa using hx) (by simpa using hy)
    rw [Set.mem_singleton_iff, ht_eq]
    unfold cardioidMap
    norm_num
  · intro hc
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine ⟨⟨-1, ?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_neg, norm_one]
    · unfold cardioidMap
      norm_num
    · rw [mem_closedBall, dist_eq_norm]
      have h : (-3 / 4 : ℂ) - -1 = 1 / 4 := by ring
      rw [h]
      norm_num [norm_div]

end

end MLC.Quadratic.FirstComponents
