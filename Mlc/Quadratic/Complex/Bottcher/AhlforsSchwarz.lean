import Mlc.Quadratic.Complex.Bottcher.SubharmonicMaxPrinciple

/-!
# Ahlfors' generalized Schwarz lemma (Schottky stage)

This file builds **Ahlfors' generalized Schwarz–Pick lemma**: a conformal metric on the
open unit disk with Gaussian curvature `≤ -1` is dominated by the Poincaré metric.  It is
step 2 of the `ℂ \ {0,1}` / Schottky route toward discharging axiom A
(`green_sublevel_translate_inter_mandelbrot_connected`); see
`SubharmonicMaxPrinciple.lean` for the analytic engine and `HyperbolicMetric.lean` for the
overall architecture.

The analytic input (subharmonic maximum principle, radial Laplacian formula, curvature `-1`
of the Poincaré density) lives in `SubharmonicMaxPrinciple.lean`.  Here we assemble the
comparison argument.

## Contents

* `exists_isMaxOn_of_le_outside` — a continuous function on an open set that is dominated,
  outside a compact subset, by its value at an interior point attains a global maximum on
  the set (the topological crux of the interior-maximum argument).
* `ahlfors_schwarz` — **Ahlfors' generalized Schwarz lemma**: a `C²` conformal metric
  `e^{u}|dz|` on the open unit disk with curvature `≤ -1` (`exp (2u) ≤ Δ u`) is dominated
  by the Poincaré density, `u ≤ log 2 - log(1 - ‖·‖²)`.
-/

namespace MLC.Quadratic

open Filter Topology Set Metric
open scoped Laplacian

/-- **Interior maximum via domination outside a compact set.** If `f` is continuous on an
open set `U`, `K ⊆ U` is compact and contains a point `z₀`, and `f z ≤ f z₀` for every
`z ∈ U` outside `K`, then `f` attains a maximum over `U` (at a point of `K`).

This packages the topological heart of Ahlfors' interior-maximum argument: the comparison
function tends to `-∞` at the boundary of the disk, so it is dominated outside a compact
sub-disk, hence its supremum is attained at an interior point. -/
theorem exists_isMaxOn_of_le_outside {U K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℝ} (hf : ContinuousOn f U) {z₀ : ℂ} (hz₀ : z₀ ∈ K)
    (hout : ∀ z ∈ U, z ∉ K → f z ≤ f z₀) :
    ∃ zmax ∈ U, IsMaxOn f U zmax := by
  have hKne : K.Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨zmax, hzmaxK, hzmax⟩ := hK.exists_isMaxOn hKne (hf.mono hKU)
  refine ⟨zmax, hKU hzmaxK, ?_⟩
  intro z hz
  by_cases hzK : z ∈ K
  · exact hzmax hzK
  · exact le_trans (hout z hz hzK) (hzmax hz₀)

open InnerProductSpace in
/-- **Ahlfors' generalized Schwarz lemma.** Let `u : ℂ → ℝ` be `C²` on the open unit disk
with the curvature condition `exp (2 u z) ≤ Δ u z` on the disk (the conformal metric
`e^{u}|dz|` has Gaussian curvature `≤ -1`). Then `u` is dominated by the Poincaré
log-density:
`u z ≤ log 2 - log (1 - ‖z‖²)` for all `z` in the disk, i.e. `e^{u(z)} ≤ 2/(1-‖z‖²)`.

The proof compares `u` against the log-density `log λ_r = log(2r) - log(r²-‖·‖²)` of the
disk of radius `r`, whose curvature is exactly `-1` (`laplacian_log_poincareDensity_radius`).
The difference `v = u - log λ_r` tends to `-∞` at the boundary sphere of radius `r`, hence
attains an interior maximum (`exists_isMaxOn_of_le_outside`); at that maximum the localized
Laplacian test (`laplacian_nonpos_of_isLocalMax_of_contDiffAt`) combined with the curvature
hypothesis forces `v ≤ 0`.  Letting `r → 1` gives the Poincaré bound. -/
theorem ahlfors_schwarz {u : ℂ → ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hcurv : ∀ z ∈ ball (0 : ℂ) 1, Real.exp (2 * u z) ≤ Δ u z)
    {z : ℂ} (hz : ‖z‖ < 1) :
    u z ≤ Real.log 2 - Real.log (1 - ‖z‖ ^ 2) := by
  have hu_cont : ContinuousOn u (ball (0 : ℂ) 1) :=
    fun x hx => (hu x hx).continuousAt.continuousWithinAt
  -- Single-radius comparison bound.
  have key : ∀ r : ℝ, ‖z‖ < r → r < 1 →
      u z ≤ Real.log (2 * r) - Real.log (r ^ 2 - ‖z‖ ^ 2) := by
    intro r hzr hr1
    have hr0 : (0 : ℝ) < r := (norm_nonneg z).trans_lt hzr
    set μ : ℂ → ℝ := fun w => Real.log (2 * r) - Real.log (r ^ 2 - ‖w‖ ^ 2) with hμdef
    set v : ℂ → ℝ := fun w => u w - μ w with hvdef
    have hcb_sub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hr1
    have hb_sub : ball (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := ball_subset_ball hr1.le
    have hzball : z ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hzr
    have hpos : ∀ w ∈ ball (0 : ℂ) r, (0 : ℝ) < r ^ 2 - ‖w‖ ^ 2 := by
      intro w hw; rw [mem_ball_zero_iff] at hw; nlinarith [norm_nonneg w]
    have hμC2 : ∀ w ∈ ball (0 : ℂ) r, ContDiffAt ℝ 2 μ w := by
      intro w hw
      have hs1 : (0 : ℝ) < r ^ 2 - ‖w‖ ^ 2 := hpos w hw
      have hF : ContDiffAt ℝ 2 (fun a : ℝ => Real.log (r ^ 2 - a)) (‖w‖ ^ 2) :=
        (Real.contDiffAt_log.mpr (ne_of_gt hs1)).comp _
          (contDiff_const.sub contDiff_id).contDiffAt
      have hlog : ContDiffAt ℝ 2 (fun w : ℂ => Real.log (r ^ 2 - ‖w‖ ^ 2)) w :=
        hF.comp w (contDiff_norm_sq ℝ).contDiffAt
      exact contDiffAt_const.sub hlog
    have hu_cont_cb : ContinuousOn u (closedBall (0 : ℂ) r) := hu_cont.mono hcb_sub
    obtain ⟨p, hp_cb, hp_max⟩ :=
      (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn ⟨0, mem_closedBall_self hr0.le⟩ hu_cont_cb
    have hCbound : ∀ w ∈ closedBall (0 : ℂ) r, u w ≤ u p := fun w hw => hp_max hw
    -- Choose the compact sub-disk of radius `r'` outside which `v` is dominated by `v z`.
    set B : ℝ := v z - u p + Real.log (2 * r) with hBdef
    set s : ℝ := max (‖z‖ ^ 2) (r ^ 2 - Real.exp B) with hsdef
    have hs_lt : s < r ^ 2 := by
      refine max_lt ?_ ?_
      · nlinarith [norm_nonneg z]
      · have := Real.exp_pos B; linarith
    have hs_nonneg : (0 : ℝ) ≤ s := le_trans (sq_nonneg _) (le_max_left _ _)
    set r' : ℝ := Real.sqrt s with hr'def
    have hr'_nonneg : 0 ≤ r' := Real.sqrt_nonneg s
    have hr'_lt_r : r' < r := by
      rw [hr'def]
      calc Real.sqrt s < Real.sqrt (r ^ 2) := Real.sqrt_lt_sqrt hs_nonneg hs_lt
        _ = r := by rw [Real.sqrt_sq hr0.le]
    have hcb'_sub : closedBall (0 : ℂ) r' ⊆ ball (0 : ℂ) r := closedBall_subset_ball hr'_lt_r
    have hz_in_K : z ∈ closedBall (0 : ℂ) r' := by
      rw [mem_closedBall_zero_iff, hr'def]
      have hzs : ‖z‖ ^ 2 ≤ s := le_max_left _ _
      nlinarith [Real.sq_sqrt hs_nonneg, Real.sqrt_nonneg s, norm_nonneg z]
    have hv_cont : ContinuousOn v (ball (0 : ℂ) r) := by
      refine ContinuousOn.sub (hu_cont.mono hb_sub) ?_
      exact fun w hw => (hμC2 w hw).continuousAt.continuousWithinAt
    have hdom : ∀ w ∈ ball (0 : ℂ) r, w ∉ closedBall (0 : ℂ) r' → v w ≤ v z := by
      intro w hw hwK
      have hwr' : r' < ‖w‖ := by rwa [mem_closedBall_zero_iff, not_le] at hwK
      have hspos := hpos w hw
      have hw2 : s < ‖w‖ ^ 2 := by
        have hlt2 : r' ^ 2 < ‖w‖ ^ 2 := by nlinarith [hr'_nonneg, norm_nonneg w]
        rwa [hr'def, Real.sq_sqrt hs_nonneg] at hlt2
      have hlt : r ^ 2 - ‖w‖ ^ 2 < Real.exp B := by
        have := le_max_right (‖z‖ ^ 2) (r ^ 2 - Real.exp B)
        rw [← hsdef] at this; linarith
      have hloglt : Real.log (r ^ 2 - ‖w‖ ^ 2) < B := by
        calc Real.log (r ^ 2 - ‖w‖ ^ 2) < Real.log (Real.exp B) := Real.log_lt_log hspos hlt
          _ = B := Real.log_exp B
      have huwC : u w ≤ u p := hCbound w (ball_subset_closedBall hw)
      have hvw : v w = u w - Real.log (2 * r) + Real.log (r ^ 2 - ‖w‖ ^ 2) := by
        simp only [hvdef, hμdef]; ring
      rw [hvw]; linarith [hBdef]
    obtain ⟨w₀, hw₀U, hw₀max⟩ :=
      exists_isMaxOn_of_le_outside (isCompact_closedBall (0 : ℂ) r') hcb'_sub hv_cont hz_in_K hdom
    -- Analyse the interior maximum `w₀`.
    have hlocmax : IsLocalMax v w₀ := hw₀max.isLocalMax (isOpen_ball.mem_nhds hw₀U)
    have hw₀ball : ‖w₀‖ < r := mem_ball_zero_iff.mp hw₀U
    have hvC2 : ContDiffAt ℝ 2 v w₀ := by
      rw [hvdef]; exact (hu w₀ (hb_sub hw₀U)).sub (hμC2 w₀ hw₀U)
    have hΔv_le : Δ v w₀ ≤ 0 := laplacian_nonpos_of_isLocalMax_of_contDiffAt hvC2 hlocmax
    have hveq : v = u + fun w => -μ w := by funext w; simp only [hvdef, Pi.add_apply]; ring
    have hΔv : Δ v w₀ = Δ u w₀ - Δ μ w₀ := by
      have hμw : ContDiffAt ℝ 2 μ w₀ := hμC2 w₀ hw₀U
      have huw : ContDiffAt ℝ 2 u w₀ := hu w₀ (hb_sub hw₀U)
      rw [hveq, huw.laplacian_add hμw.neg, laplacian_neg hμw]; ring
    have hΔu_ge : Real.exp (2 * u w₀) ≤ Δ u w₀ := hcurv w₀ (hb_sub hw₀U)
    have hΔμ : Δ μ w₀ = (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) ^ 2 := by
      rw [hμdef]; exact laplacian_log_poincareDensity_radius hr0 hw₀ball
    have hlam_pos : (0 : ℝ) < 2 * r / (r ^ 2 - ‖w₀‖ ^ 2) :=
      div_pos (by linarith) (hpos w₀ hw₀U)
    have hexp_le : Real.exp (2 * u w₀) ≤ (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) ^ 2 := by
      calc Real.exp (2 * u w₀) ≤ Δ u w₀ := hΔu_ge
        _ ≤ Δ μ w₀ := by linarith [hΔv, hΔv_le]
        _ = _ := hΔμ
    have hsq : Real.exp (2 * u w₀) = Real.exp (u w₀) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hexpu_le : Real.exp (u w₀) ≤ 2 * r / (r ^ 2 - ‖w₀‖ ^ 2) := by
      rw [hsq] at hexp_le
      nlinarith [hexp_le, Real.exp_pos (u w₀), hlam_pos]
    have hu_le_log : u w₀ ≤ Real.log (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) := by
      have := Real.log_le_log (Real.exp_pos _) hexpu_le
      rwa [Real.log_exp] at this
    have hμ_eq : μ w₀ = Real.log (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) := by
      simp only [hμdef]
      rw [Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (hpos w₀ hw₀U))]
    have hvw₀_le : v w₀ ≤ 0 := by
      have hle : u w₀ ≤ μ w₀ := by rw [hμ_eq]; exact hu_le_log
      simp only [hvdef]; linarith
    have hvz_le : v z ≤ v w₀ := hw₀max hzball
    have hfin : v z ≤ 0 := le_trans hvz_le hvw₀_le
    simp only [hvdef, hμdef] at hfin
    linarith
  -- Let `r → 1`.
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      u z ≤ Real.log (2 * r) - Real.log (r ^ 2 - ‖z‖ ^ 2) := by
    filter_upwards [(eventually_gt_nhds hz).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hzr hr1
    exact key r hzr (mem_Iio.mp hr1)
  have hcontat : ContinuousAt
      (fun r : ℝ => Real.log (2 * r) - Real.log (r ^ 2 - ‖z‖ ^ 2)) 1 := by
    have hpos1 : (0 : ℝ) < (1 : ℝ) ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    refine ContinuousAt.sub ?_ ?_
    · have h : ContinuousAt Real.log (2 * (1 : ℝ)) := Real.continuousAt_log (by norm_num)
      exact h.comp (continuousAt_const.mul continuousAt_id)
    · have h : ContinuousAt Real.log ((1 : ℝ) ^ 2 - ‖z‖ ^ 2) := Real.continuousAt_log hpos1.ne'
      exact ContinuousAt.comp (f := fun r : ℝ => r ^ 2 - ‖z‖ ^ 2) h
        (((continuous_pow 2).continuousAt).sub continuousAt_const)
  have htend : Tendsto (fun r : ℝ => Real.log (2 * r) - Real.log (r ^ 2 - ‖z‖ ^ 2))
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2 - Real.log (1 - ‖z‖ ^ 2))) := by
    have h := hcontat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    simpa using h
  exact ge_of_tendsto htend hev

end MLC.Quadratic
