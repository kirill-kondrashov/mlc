/-
Copyright (c) 2025 The MLC Project Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Analyticity of the true-Böttcher correction product

This file supplies the analyticity half of the far-exterior true Böttcher
coordinate build (frontier axiom 1, `external_ray_map_exists`).  The genuine
holomorphic Böttcher coordinate at `c` is `z · ∏ₖ (1 + c/z_k²)^{1/2^{k+1}}`,
whose ordered partial products are the already-defined
`finiteProductBottcherRatio c n` (built from the branch-safe
`nearOneCorrectionFactor c k`).  The remaining open convergence seam is
`CorrectionProductConvergesOnExterior`.

Here we prove, decoupled from that convergence estimate, that each correction
factor and hence each finite partial product is analytic wherever the branch-safe
base lies in the slit plane.  This is the analytic-uniform-limit input for the
eventual analyticity of the coordinate limit and is reusable regardless of the
route taken to establish convergence.

## Main results

* `analyticAt_iterate_quadratic_map` — every iterate `(quadratic_map c)^[N]` is
  entire.
* `nearOneCorrectionFactor_analyticAt` — each near-one correction factor is
  analytic at `z` when `z ≠ 0`, the base ratio is nonzero, and the branch-safe
  base is in the slit plane.
* `finiteProductBottcherRatio_analyticAt` — each finite partial product is
  analytic under the same pointwise hypotheses on all earlier factors.
-/

namespace MLC

open Quadratic Complex Topology Set Filter

/-- The quadratic map `z ↦ z² + c` is entire. -/
lemma analyticAt_quadratic_map (c z : ℂ) : AnalyticAt ℂ (quadratic_map c) z := by
  unfold quadratic_map
  exact (analyticAt_id.pow 2).add analyticAt_const

/-- Every iterate of the quadratic map is entire. -/
lemma analyticAt_iterate_quadratic_map (c : ℂ) :
    ∀ (N : ℕ) (z : ℂ), AnalyticAt ℂ ((quadratic_map c)^[N]) z
  | 0, z => by
      simpa using (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) z)
  | N + 1, z => by
      rw [Function.iterate_succ']
      exact (analyticAt_quadratic_map c _).comp (analyticAt_iterate_quadratic_map c N z)

/-- **Analyticity of a single branch-safe correction factor.**  Where the base
ratio `(quadratic_map c)^[N] z / z^{2^N}` is nonzero and the branch-safe base
`1 + (c/z^{2^{N+1}})/(base ratio)²` avoids the negative real axis, the principal
`1/2^{N+1}` power defining `nearOneCorrectionFactor c N` is analytic. -/
lemma nearOneCorrectionFactor_analyticAt (c : ℂ) (N : ℕ) {z : ℂ}
    (hz : z ≠ 0)
    (hg : (quadratic_map c)^[N] z / z ^ (2 ^ N) ≠ 0)
    (hbase : (1 + (c / z ^ (2 ^ (N + 1))) /
        ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (nearOneCorrectionFactor c N) z := by
  have hz1 : (z : ℂ) ^ (2 ^ (N + 1)) ≠ 0 := pow_ne_zero _ hz
  have hz0 : (z : ℂ) ^ (2 ^ N) ≠ 0 := pow_ne_zero _ hz
  have hnum : AnalyticAt ℂ (fun w : ℂ => c / w ^ (2 ^ (N + 1))) z :=
    analyticAt_const.div (analyticAt_id.pow _) hz1
  have hden : AnalyticAt ℂ (fun w : ℂ => (quadratic_map c)^[N] w / w ^ (2 ^ N)) z :=
    (analyticAt_iterate_quadratic_map c N z).div (analyticAt_id.pow _) hz0
  have hdensq_ne : ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 ≠ 0 := pow_ne_zero 2 hg
  have hfrac : AnalyticAt ℂ
      (fun w : ℂ => (c / w ^ (2 ^ (N + 1))) /
        ((quadratic_map c)^[N] w / w ^ (2 ^ N)) ^ 2) z :=
    hnum.div (hden.pow 2) hdensq_ne
  have hbaseA : AnalyticAt ℂ
      (fun w : ℂ => 1 + (c / w ^ (2 ^ (N + 1))) /
        ((quadratic_map c)^[N] w / w ^ (2 ^ N)) ^ 2) z :=
    analyticAt_const.add hfrac
  have hcpow := AnalyticAt.cpow hbaseA
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((2 : ℂ) ^ (N + 1))⁻¹) z) hbase
  simpa [nearOneCorrectionFactor] using hcpow

/-- **Analyticity of the finite Böttcher partial product.**  A finite product of
correction factors is analytic wherever every factor is. -/
lemma finiteProductBottcherRatio_analyticAt (c : ℂ) (n : ℕ) {z : ℂ}
    (h : ∀ k ∈ Finset.range n, AnalyticAt ℂ (nearOneCorrectionFactor c k) z) :
    AnalyticAt ℂ (finiteProductBottcherRatio c n) z := by
  unfold finiteProductBottcherRatio
  exact Finset.analyticAt_fun_prod (Finset.range n) h

/-- **Base simplification.**  For `z ≠ 0` and a nonzero `N`-th iterate, the
branch-safe correction base telescopes to the classical Böttcher form
`c / z_N²`, where `z_N = (quadratic_map c)^[N] z`. -/
lemma nearOneCorrectionFactor_base_eq (c : ℂ) (N : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hzN : (quadratic_map c)^[N] z ≠ 0) :
    (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2
      = c / ((quadratic_map c)^[N] z) ^ 2 := by
  have hz1 : (z : ℂ) ^ (2 ^ (N + 1)) ≠ 0 := pow_ne_zero _ hz
  have hpow : ((z : ℂ) ^ (2 ^ N)) ^ 2 = z ^ (2 ^ (N + 1)) := by
    rw [← pow_mul, ← pow_succ]
  rw [div_pow, hpow]
  field_simp

/-- The near-one correction factor in classical Böttcher form
`(1 + c / z_N²)^{1/2^{N+1}}`. -/
lemma nearOneCorrectionFactor_eq_orbit (c : ℂ) (N : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hzN : (quadratic_map c)^[N] z ≠ 0) :
    nearOneCorrectionFactor c N z
      = (1 + c / ((quadratic_map c)^[N] z) ^ 2) ^ ((2 : ℂ) ^ (N + 1))⁻¹ := by
  unfold nearOneCorrectionFactor
  rw [nearOneCorrectionFactor_base_eq c N hz hzN]

/-- **Uniform far-exterior analyticity of a correction factor.**  On the region
`{‖c‖ + 1 ≤ ‖z‖} ∩ {‖c‖ < ‖z‖²}` every hypothesis of
`nearOneCorrectionFactor_analyticAt` is automatic: the orbit-norm lower bound
`‖z_N‖ ≥ ‖z‖` (`iterate_quadratic_map_norm_ge`) gives `z ≠ 0`, `z_N ≠ 0`, nonzero
base ratio, and `‖c/z_N²‖ ≤ ‖c‖/‖z‖² < 1`, placing the base in the slit plane. -/
lemma nearOneCorrectionFactor_analyticAt_of_norm_gt (c : ℂ) (N : ℕ) {z : ℂ}
    (hc1 : ‖c‖ + 1 ≤ ‖z‖) (hc2 : ‖c‖ < ‖z‖ ^ 2) :
    AnalyticAt ℂ (nearOneCorrectionFactor c N) z := by
  have hzpos : 0 < ‖z‖ := by have := norm_nonneg c; linarith
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have hznge : ‖z‖ ≤ ‖(quadratic_map c)^[N] z‖ := iterate_quadratic_map_norm_ge c z N hc1
  have hzNpos : 0 < ‖(quadratic_map c)^[N] z‖ := lt_of_lt_of_le hzpos hznge
  have hzN : (quadratic_map c)^[N] z ≠ 0 := norm_pos_iff.mp hzNpos
  have hg : (quadratic_map c)^[N] z / z ^ (2 ^ N) ≠ 0 := div_ne_zero hzN (pow_ne_zero _ hz)
  have hbase : (1 + (c / z ^ (2 ^ (N + 1))) /
      ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2) ∈ Complex.slitPlane := by
    rw [nearOneCorrectionFactor_base_eq c N hz hzN]
    apply mem_slitPlane_of_norm_sub_one_lt_one
    have hnorm : ‖(1 + c / ((quadratic_map c)^[N] z) ^ 2) - 1‖
        = ‖c‖ / ‖(quadratic_map c)^[N] z‖ ^ 2 := by
      rw [add_sub_cancel_left, norm_div, norm_pow]
    rw [hnorm]
    have h1 : ‖c‖ / ‖(quadratic_map c)^[N] z‖ ^ 2 ≤ ‖c‖ / ‖z‖ ^ 2 := by
      gcongr
    have h2 : ‖c‖ / ‖z‖ ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; exact hc2
    linarith
  exact nearOneCorrectionFactor_analyticAt c N hz hg hbase

/-- **Uniform far-exterior analyticity of the finite partial product.** -/
lemma finiteProductBottcherRatio_analyticAt_of_norm_gt (c : ℂ) (n : ℕ) {z : ℂ}
    (hc1 : ‖c‖ + 1 ≤ ‖z‖) (hc2 : ‖c‖ < ‖z‖ ^ 2) :
    AnalyticAt ℂ (finiteProductBottcherRatio c n) z :=
  finiteProductBottcherRatio_analyticAt c n
    (fun k _ => nearOneCorrectionFactor_analyticAt_of_norm_gt c k hc1 hc2)

/-- **M-test term bound.**  On the far exterior `{‖c‖+1 ≤ ‖z‖}` with the base argument
under control (`‖c‖/‖z‖² ≤ ½`), each correction factor deviates from `1` by at most
`3·2^{-(N+1)}·(‖c‖/‖z‖²)`.  Writing the factor as `exp(a·log(1+w))` with
`w = c/z_N²` (`‖w‖ ≤ ‖c‖/‖z‖²`) and `a = 2^{-(N+1)}`, the estimate combines
`‖log(1+w)‖ ≤ (3/2)‖w‖` and `‖exp ζ − 1‖ ≤ 2‖ζ‖` (for `‖ζ‖ ≤ 1`).  The `2^{-(N+1)}`
factor makes `∑_N` converge with uniform sum `≤ 3·(‖c‖/‖z‖²)`. -/
lemma nearOneCorrectionFactor_sub_one_norm_le (c : ℂ) (N : ℕ) {z : ℂ}
    (hc1 : ‖c‖ + 1 ≤ ‖z‖) (hq : ‖c‖ / ‖z‖ ^ 2 ≤ 1 / 2) :
    ‖nearOneCorrectionFactor c N z - 1‖
      ≤ 3 * ((2 : ℝ) ^ (N + 1))⁻¹ * (‖c‖ / ‖z‖ ^ 2) := by
  have hzpos : 0 < ‖z‖ := by have := norm_nonneg c; linarith
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have hznge : ‖z‖ ≤ ‖(quadratic_map c)^[N] z‖ := iterate_quadratic_map_norm_ge c z N hc1
  have hzNpos : 0 < ‖(quadratic_map c)^[N] z‖ := lt_of_lt_of_le hzpos hznge
  have hzN : (quadratic_map c)^[N] z ≠ 0 := norm_pos_iff.mp hzNpos
  have hfac : nearOneCorrectionFactor c N z
      = (1 + c / ((quadratic_map c)^[N] z) ^ 2) ^ ((2 : ℂ) ^ (N + 1))⁻¹ :=
    nearOneCorrectionFactor_eq_orbit c N hz hzN
  set w : ℂ := c / ((quadratic_map c)^[N] z) ^ 2 with hw_def
  set a : ℂ := ((2 : ℂ) ^ (N + 1))⁻¹ with ha_def
  have haR : ((2 : ℝ) ^ (N + 1))⁻¹ = ‖a‖ := by
    rw [ha_def, norm_inv, norm_pow, Complex.norm_ofNat]
  have haR_nonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ (N + 1))⁻¹ := by positivity
  have haR_half : ((2 : ℝ) ^ (N + 1))⁻¹ ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [inv_le_iff_one_le_mul₀ (by positivity)]; linarith
  -- ‖w‖ ≤ ‖c‖/‖z‖² ≤ 1/2
  have hwnorm : ‖w‖ = ‖c‖ / ‖(quadratic_map c)^[N] z‖ ^ 2 := by
    rw [hw_def, norm_div, norm_pow]
  have hwle : ‖w‖ ≤ ‖c‖ / ‖z‖ ^ 2 := by rw [hwnorm]; gcongr
  have hwhalf : ‖w‖ ≤ 1 / 2 := le_trans hwle hq
  have hwlt1 : ‖w‖ < 1 := lt_of_le_of_lt hwhalf (by norm_num)
  have hslit : (1 + w) ∈ Complex.slitPlane :=
    mem_slitPlane_of_norm_sub_one_lt_one (by simpa using hwlt1)
  have hbase_ne : (1 + w) ≠ 0 := Complex.slitPlane_ne_zero hslit
  -- factor = exp ζ, ζ = log(1+w) * a
  have hcpow : (1 + w) ^ a = Complex.exp (Complex.log (1 + w) * a) :=
    Complex.cpow_def_of_ne_zero hbase_ne a
  set ζ : ℂ := Complex.log (1 + w) * a with hζ_def
  have hlog : ‖Complex.log (1 + w)‖ ≤ (3 / 2) * ‖w‖ :=
    Complex.norm_log_one_add_half_le_self hwhalf
  have hζnorm : ‖ζ‖ ≤ (3 / 2) * ‖w‖ * ((2 : ℝ) ^ (N + 1))⁻¹ := by
    rw [hζ_def, norm_mul, haR]
    exact mul_le_mul_of_nonneg_right hlog (norm_nonneg a)
  have hζle1 : ‖ζ‖ ≤ 1 := by
    have : (3 / 2) * ‖w‖ * ((2 : ℝ) ^ (N + 1))⁻¹ ≤ 1 := by
      nlinarith [hwhalf, haR_half, haR_nonneg, norm_nonneg w]
    linarith [hζnorm]
  have hexp : ‖Complex.exp ζ - 1‖ ≤ 2 * ‖ζ‖ := by
    have h := Complex.norm_exp_sub_one_sub_id_le hζle1
    have htri : ‖Complex.exp ζ - 1‖ ≤ ‖Complex.exp ζ - 1 - ζ‖ + ‖ζ‖ := by
      have := norm_add_le (Complex.exp ζ - 1 - ζ) ζ
      simpa [sub_add_cancel] using this
    have hsq : ‖ζ‖ ^ 2 ≤ ‖ζ‖ :=
      by nlinarith [mul_nonneg (norm_nonneg ζ) (by linarith [hζle1] : (0:ℝ) ≤ 1 - ‖ζ‖)]
    linarith [h, htri, hsq]
  rw [hfac, hcpow]
  calc ‖Complex.exp ζ - 1‖
      ≤ 2 * ‖ζ‖ := hexp
    _ ≤ 2 * ((3 / 2) * ‖w‖ * ((2 : ℝ) ^ (N + 1))⁻¹) := by linarith [hζnorm]
    _ ≤ 3 * ((2 : ℝ) ^ (N + 1))⁻¹ * (‖c‖ / ‖z‖ ^ 2) := by
        have hqnn : (0 : ℝ) ≤ ‖c‖ / ‖z‖ ^ 2 := by positivity
        nlinarith [hwle, haR_nonneg, hqnn, norm_nonneg w,
          mul_le_mul_of_nonneg_right hwle haR_nonneg]

/-- **Convergence seam discharged on the far exterior.**  Whenever `R` is large
enough (`‖c‖+1 ≤ R` and `2‖c‖ ≤ R²`), the near-one correction product converges
locally uniformly on `{z | R < ‖z‖}` to `correctionProductBottcherRatio c`.

Proof: a Weierstrass M-test.  The per-term bound
`nearOneCorrectionFactor_sub_one_norm_le` majorizes `‖factor − 1‖` by the
summable geometric sequence `3·2^{-(n+1)}·(‖c‖/R²)`, so
`hasProdLocallyUniformlyOn_nat_one_add` yields locally uniform convergence to the
unconditional product `∏' i, nearOneCorrectionFactor c i z`.  That equals the
conditional `correctionProductBottcherRatio c z` because pointwise
multipliability collapses the conditional filter to the unconditional one
(`tprod_eq_of_multipliable_unconditional`). -/
lemma correctionProductConvergesOnExterior_of_norm_bounds (c : ℂ) {R : ℝ}
    (hR1 : ‖c‖ + 1 ≤ R) (hR2 : 2 * ‖c‖ ≤ R ^ 2) :
    CorrectionProductConvergesOnExterior c R := by
  set K : Set ℂ := {z : ℂ | R < ‖z‖} with hK_def
  have hRpos : 0 < R := by have := norm_nonneg c; linarith
  have hKopen : IsOpen K := isOpen_lt continuous_const continuous_norm
  -- far-exterior facts for `z ∈ K`
  have hfacts : ∀ z ∈ K, ‖c‖ + 1 ≤ ‖z‖ ∧ ‖c‖ / ‖z‖ ^ 2 ≤ 1 / 2 ∧ ‖c‖ < ‖z‖ ^ 2 := by
    intro z hz
    have hzn : R < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := lt_trans hRpos hzn
    have hzc1 : ‖c‖ + 1 ≤ ‖z‖ := by linarith
    have hzsq : R ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [hRpos, hzn]
    have hzsqpos : 0 < ‖z‖ ^ 2 := by positivity
    have hhalf : ‖c‖ / ‖z‖ ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ hzsqpos]; nlinarith [hR2, hzsq]
    have hlt : ‖c‖ < ‖z‖ ^ 2 := by nlinarith [hzc1, norm_nonneg c]
    exact ⟨hzc1, hhalf, hlt⟩
  -- summable geometric majorant
  set u : ℕ → ℝ := fun n => 3 * ((2 : ℝ) ^ (n + 1))⁻¹ * (‖c‖ / R ^ 2) with hu_def
  have hu : Summable u := by
    have hgeo : Summable (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hmul : Summable (fun n : ℕ => (3 * (‖c‖ / R ^ 2) * (2 : ℝ)⁻¹) * ((2 : ℝ)⁻¹) ^ n) :=
      hgeo.mul_left _
    refine hmul.congr (fun n => ?_)
    simp only [hu_def]
    rw [show ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ)⁻¹) ^ (n + 1) from (inv_pow 2 (n + 1)).symm,
      pow_succ]
    ring
  -- per-term uniform bound on K
  have hbound : ∀ᶠ n in Filter.atTop,
      ∀ z ∈ K, ‖(fun z => nearOneCorrectionFactor c n z - 1) z‖ ≤ u n := by
    refine Filter.Eventually.of_forall (fun n z hz => ?_)
    obtain ⟨hzc1, hhalf, _⟩ := hfacts z hz
    have hzn : R < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := lt_trans hRpos hzn
    have hmono : ‖c‖ / ‖z‖ ^ 2 ≤ ‖c‖ / R ^ 2 := by
      apply div_le_div_of_nonneg_left (norm_nonneg c) (by positivity)
      nlinarith [hRpos, hzn]
    have hstep :
        ‖nearOneCorrectionFactor c n z - 1‖
          ≤ 3 * ((2 : ℝ) ^ (n + 1))⁻¹ * (‖c‖ / R ^ 2) := by
      refine le_trans (nearOneCorrectionFactor_sub_one_norm_le c n hzc1 hhalf) ?_
      gcongr
    simpa [hu_def] using hstep
  -- continuity of each factor on K (from analyticity)
  have hcts : ∀ n, ContinuousOn (fun z => nearOneCorrectionFactor c n z - 1) K := by
    intro n
    refine ContinuousOn.sub (fun z hz => ?_) continuousOn_const
    obtain ⟨hzc1, _, hlt⟩ := hfacts z hz
    exact ((nearOneCorrectionFactor_analyticAt_of_norm_gt c n hzc1 hlt).continuousAt).continuousWithinAt
  -- Weierstrass M-test
  have hLU0 := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun n z => nearOneCorrectionFactor c n z - 1) (K := K) hKopen hu hbound hcts
  have hfeq : (fun (n : ℕ) (x : ℂ) => 1 + (nearOneCorrectionFactor c n x - 1))
      = (fun n x => nearOneCorrectionFactor c n x) := by funext n x; ring
  have hgeq : (fun (x : ℂ) => ∏' i, (1 + (nearOneCorrectionFactor c i x - 1)))
      = (fun x => ∏' i, nearOneCorrectionFactor c i x) := by
    funext x; exact tprod_congr (fun i => by ring)
  rw [hfeq, hgeq] at hLU0
  -- identify the unconditional limit with the conditional correction ratio
  have hEqOn : Set.EqOn (fun x => ∏' i, nearOneCorrectionFactor c i x)
      (correctionProductBottcherRatio c) K := by
    intro x hx
    have hmul : Multipliable (fun n => nearOneCorrectionFactor c n x) :=
      (hLU0.hasProd hx).multipliable
    show (∏' i, nearOneCorrectionFactor c i x) = correctionProductBottcherRatio c x
    rw [correctionProductBottcherRatio,
      tprod_eq_of_multipliable_unconditional (L := SummationFilter.conditional ℕ) hmul]
  exact TendstoLocallyUniformlyOn.congr_right hLU0 hEqOn

/-- Each analytic partial product is differentiable on the far exterior. -/
lemma finiteProductBottcherRatio_differentiableOn_exterior (c : ℂ) (n : ℕ) {R : ℝ}
    (hR1 : ‖c‖ + 1 ≤ R) :
    DifferentiableOn ℂ (finiteProductBottcherRatio c n) {z : ℂ | R < ‖z‖} := by
  intro z hz
  have hzn : R < ‖z‖ := hz
  have hzc1 : ‖c‖ + 1 ≤ ‖z‖ := by linarith
  have hlt : ‖c‖ < ‖z‖ ^ 2 := by nlinarith [hzc1, norm_nonneg c]
  exact ((finiteProductBottcherRatio_analyticAt_of_norm_gt c n hzc1 hlt).differentiableAt).differentiableWithinAt

/-- **Analyticity of the limit coordinate ratio.**  The ordered correction product
`correctionProductBottcherRatio c` is holomorphic on the far exterior
`{z | R < ‖z‖}`, being the locally-uniform limit of the analytic partial products
`finiteProductBottcherRatio c n` (Weierstrass / `TendstoLocallyUniformlyOn.differentiableOn`). -/
lemma correctionProductBottcherRatio_differentiableOn_exterior (c : ℂ) {R : ℝ}
    (hR1 : ‖c‖ + 1 ≤ R) (hR2 : 2 * ‖c‖ ≤ R ^ 2) :
    DifferentiableOn ℂ (correctionProductBottcherRatio c) {z : ℂ | R < ‖z‖} := by
  have hLU := (correctionProductConvergesOnExterior_of_norm_bounds c hR1 hR2).tendsto_finiteProductRatio
  refine hLU.differentiableOn ?_ (isOpen_lt continuous_const continuous_norm)
  exact Filter.Eventually.of_forall
    (fun n => finiteProductBottcherRatio_differentiableOn_exterior c n hR1)

/-- Pointwise analyticity of the limit coordinate ratio on the far exterior. -/
lemma correctionProductBottcherRatio_analyticAt_of_norm_gt (c : ℂ) {R : ℝ}
    (hR1 : ‖c‖ + 1 ≤ R) (hR2 : 2 * ‖c‖ ≤ R ^ 2) {z : ℂ} (hz : R < ‖z‖) :
    AnalyticAt ℂ (correctionProductBottcherRatio c) z :=
  (correctionProductBottcherRatio_differentiableOn_exterior c hR1 hR2).analyticAt
    ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)

/-- **Analyticity of the full true-Böttcher coordinate.**  The candidate coordinate
`correctionProductBottcherApprox c z = z · correctionProductBottcherRatio c z` is
holomorphic on the far exterior `{z | R < ‖z‖}`. -/
lemma correctionProductBottcherApprox_analyticAt_of_norm_gt (c : ℂ) {R : ℝ}
    (hR1 : ‖c‖ + 1 ≤ R) (hR2 : 2 * ‖c‖ ≤ R ^ 2) {z : ℂ} (hz : R < ‖z‖) :
    AnalyticAt ℂ (correctionProductBottcherApprox c) z := by
  have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have hratio := correctionProductBottcherRatio_analyticAt_of_norm_gt c hR1 hR2 hz
  have hfun : correctionProductBottcherApprox c
      = fun w : ℂ => w * correctionProductBottcherRatio c w := rfl
  rw [hfun]
  exact hid.mul hratio

end MLC
