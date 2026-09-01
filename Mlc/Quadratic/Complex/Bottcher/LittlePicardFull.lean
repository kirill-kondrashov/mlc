import Mlc.Quadratic.Complex.Bottcher.LittlePicard

/-!
# Full little Picard theorem (entire ⟹ constant) via a density-form Ahlfors lemma

`LittlePicard.lean` proved the *immersion* form: no entire immersion omits `{0,1}`
(`false_of_entire_immersion_omitting_two`).  The full little Picard theorem — every entire
function omitting two values is **constant** — additionally has to tolerate the *critical
points* of `f`, where the pulled-back log-density `log‖f'‖ → -∞`.  The immersion Ahlfors
lemma (`ahlfors_schwarz`) requires the metric to be `C²` on the whole disk, so it cannot be
applied when `f'` has zeros.

The clean fix is a **density-form** Ahlfors lemma, `ahlfors_schwarz_density`: instead of a
log-density `u` that blows up at the zeros, we compare the *density* `ρ = e^u ≥ 0` (which
extends continuously by `0` across the zeros) against the disk Poincaré density.  The trick
is the auxiliary function

  `V w = ρ w · (r² − ‖w‖²) / (2r)`  ( `= ρ / λ_r` in the interior),

which is continuous on the *closed* disk of radius `r`, vanishes on the boundary sphere, and
hence attains its maximum at an interior point `w₀`.  If `ρ z > 0` that maximum is positive,
so `ρ w₀ > 0`, and `v = log ρ − μ` has an interior local maximum where `ρ` is `C²`; the
localized Laplacian test forces `ρ ≤ λ_r`.  Letting `r → 1` gives the Poincaré bound.  Zeros
of `ρ` are automatically excluded from the maximum, so no `-∞` bookkeeping is needed.

Feeding the pulled-back density `ρ = (√(1/1000)·σ)(f ·)·‖f'‖` (continuous everywhere, `C²`
with curvature `≤ -1` wherever `f' ≠ 0`) into this lemma and rescaling gives:

* `ahlfors_schwarz_density` — the density-form Ahlfors–Schwarz lemma;
* `little_picard` — an entire function omitting `{0,1}` is constant.

All results are sorry-free and use only the Lean-core axioms.
-/

namespace MLC.Quadratic

open Complex Metric Set Filter Topology
open scoped Laplacian

open InnerProductSpace in
/-- **Density-form Ahlfors–Schwarz lemma.** Let `ρ : ℂ → ℝ` be continuous and nonnegative on
the open unit disk, `C²` in its logarithm wherever `ρ ≠ 0`, and satisfy the curvature-`≤ -1`
condition `ρ² ≤ Δ (log ρ)` wherever `ρ ≠ 0`.  Then `ρ` is dominated by the disk Poincaré
density: `ρ z ≤ 2 / (1 - ‖z‖²)` for all `‖z‖ < 1`.

Unlike `ahlfors_schwarz`, this version tolerates **zeros** of `ρ` (critical points of a
pulled-back metric): they extend continuously and are automatically excluded from the
interior maximum of the comparison function. -/
theorem ahlfors_schwarz_density {ρ : ℂ → ℝ}
    (hρcont : ContinuousOn ρ (ball (0 : ℂ) 1))
    (hρnonneg : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ ρ w)
    (hρC2 : ∀ w ∈ ball (0 : ℂ) 1, ρ w ≠ 0 → ContDiffAt ℝ 2 (fun x => Real.log (ρ x)) w)
    (hcurv : ∀ w ∈ ball (0 : ℂ) 1, ρ w ≠ 0 →
      ρ w ^ 2 ≤ Δ (fun x => Real.log (ρ x)) w)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ρ z ≤ 2 / (1 - ‖z‖ ^ 2) := by
  -- Single-radius comparison bound `ρ z ≤ 2r/(r²-‖z‖²)`.
  have key : ∀ r : ℝ, ‖z‖ < r → r < 1 → ρ z ≤ 2 * r / (r ^ 2 - ‖z‖ ^ 2) := by
    intro r hzr hr1
    have hr0 : (0 : ℝ) < r := (norm_nonneg z).trans_lt hzr
    have hcb_sub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hr1
    have hzr2 : ‖z‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg z]
    have hzpos : (0 : ℝ) < r ^ 2 - ‖z‖ ^ 2 := by linarith
    rcases eq_or_lt_of_le (hρnonneg z (mem_ball_zero_iff.mpr (hzr.trans hr1))) with hz0 | hzρ
    · rw [← hz0]; positivity
    -- Auxiliary `V w = ρ w · (r² − ‖w‖²)/(2r)`, continuous on the closed disk, `0` on ∂.
    set V : ℂ → ℝ := fun w => ρ w * (r ^ 2 - ‖w‖ ^ 2) / (2 * r) with hVdef
    have hVcont : ContinuousOn V (closedBall (0 : ℂ) r) := by
      refine ContinuousOn.div ?_ continuousOn_const (fun _ _ => by positivity)
      exact (hρcont.mono hcb_sub).mul
        (continuousOn_const.sub ((continuous_norm.continuousOn).pow 2))
    obtain ⟨w₀, hw₀cb, hw₀max⟩ :=
      (isCompact_closedBall (0 : ℂ) r).exists_isMaxOn ⟨0, mem_closedBall_self hr0.le⟩ hVcont
    have hzcb : z ∈ closedBall (0 : ℂ) r := mem_closedBall_zero_iff.mpr hzr.le
    have hVz_pos : 0 < V z := by rw [hVdef]; positivity
    have hVw₀_pos : 0 < V w₀ := lt_of_lt_of_le hVz_pos (hw₀max hzcb)
    have hw₀mem : w₀ ∈ ball (0 : ℂ) 1 := hcb_sub hw₀cb
    have hfac_pos : 0 < r ^ 2 - ‖w₀‖ ^ 2 := by
      by_contra h
      push_neg at h
      have : V w₀ ≤ 0 := by
        rw [hVdef]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (hρnonneg w₀ hw₀mem) h) (by positivity)
      linarith
    have hw₀ball : ‖w₀‖ < r := by nlinarith [norm_nonneg w₀]
    have hρw₀_pos : 0 < ρ w₀ := by
      by_contra h
      push_neg at h
      have hz00 : ρ w₀ = 0 := le_antisymm h (hρnonneg w₀ hw₀mem)
      simp [hVdef, hz00] at hVw₀_pos
    have hρw₀ne : ρ w₀ ≠ 0 := ne_of_gt hρw₀_pos
    -- Poincaré log-density `μ` and comparison `v = log ρ − μ`; `v = log V` where `ρ > 0`.
    set μ : ℂ → ℝ := fun w => Real.log (2 * r) - Real.log (r ^ 2 - ‖w‖ ^ 2) with hμdef
    set v : ℂ → ℝ := fun w => Real.log (ρ w) - μ w with hvdef
    have hlogV_eq : ∀ w ∈ ball (0 : ℂ) r, ρ w ≠ 0 → Real.log (V w) = v w := by
      intro w hw hρw
      have hw1 : (0 : ℝ) < r ^ 2 - ‖w‖ ^ 2 := by
        rw [mem_ball_zero_iff] at hw; nlinarith [norm_nonneg w]
      have hρwpos : 0 < ρ w :=
        lt_of_le_of_ne (hρnonneg w (ball_subset_ball hr1.le hw)) (Ne.symm hρw)
      rw [hVdef, hvdef, hμdef, Real.log_div (by positivity) (by positivity),
        Real.log_mul (ne_of_gt hρwpos) (by positivity)]
      ring
    have hw₀nhds : ball (0 : ℂ) r ∈ 𝓝 w₀ := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw₀ball)
    have hVev : ∀ᶠ w in 𝓝 w₀, V w ≤ V w₀ := by
      filter_upwards [hw₀nhds] with w hw; exact hw₀max (ball_subset_closedBall hw)
    have hcontw₀ : ContinuousAt ρ w₀ := hρcont.continuousAt (isOpen_ball.mem_nhds hw₀mem)
    have hρpos_nhds : ∀ᶠ w in 𝓝 w₀, 0 < ρ w :=
      continuousAt_const.eventually_lt hcontw₀ (by simpa using hρw₀_pos)
    have hvlocmax : IsLocalMax v w₀ := by
      filter_upwards [hVev, hρpos_nhds, hw₀nhds] with w hVw hρw hwball
      have hwr : (0 : ℝ) < r ^ 2 - ‖w‖ ^ 2 := by
        rw [mem_ball_zero_iff] at hwball; nlinarith [norm_nonneg w]
      have hVwpos : 0 < V w := by
        rw [hVdef]; exact div_pos (mul_pos hρw hwr) (by positivity)
      rw [show v w = Real.log (V w) from (hlogV_eq w hwball (ne_of_gt hρw)).symm,
        show v w₀ = Real.log (V w₀) from (hlogV_eq w₀ (mem_ball_zero_iff.mpr hw₀ball) hρw₀ne).symm]
      exact Real.log_le_log hVwpos hVw
    -- `v` is `C²` at `w₀`; localized Laplacian test.
    have hμC2 : ContDiffAt ℝ 2 μ w₀ := by
      have hF : ContDiffAt ℝ 2 (fun a : ℝ => Real.log (r ^ 2 - a)) (‖w₀‖ ^ 2) :=
        (Real.contDiffAt_log.mpr (ne_of_gt hfac_pos)).comp _
          (contDiff_const.sub contDiff_id).contDiffAt
      have hlog : ContDiffAt ℝ 2 (fun w : ℂ => Real.log (r ^ 2 - ‖w‖ ^ 2)) w₀ :=
        hF.comp w₀ (contDiff_norm_sq ℝ).contDiffAt
      exact contDiffAt_const.sub hlog
    have hlogρC2 : ContDiffAt ℝ 2 (fun x => Real.log (ρ x)) w₀ := hρC2 w₀ hw₀mem hρw₀ne
    have hvC2 : ContDiffAt ℝ 2 v w₀ := hlogρC2.sub hμC2
    have hΔv_le : Δ v w₀ ≤ 0 := laplacian_nonpos_of_isLocalMax_of_contDiffAt hvC2 hvlocmax
    have hveq : v = (fun x => Real.log (ρ x)) + fun w => -μ w := by
      funext w; simp only [hvdef, Pi.add_apply]; ring
    have hΔv : Δ v w₀ = Δ (fun x => Real.log (ρ x)) w₀ - Δ μ w₀ := by
      rw [hveq, hlogρC2.laplacian_add hμC2.neg, laplacian_neg hμC2]; ring
    have hΔμ : Δ μ w₀ = (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) ^ 2 := by
      rw [hμdef]; exact laplacian_log_poincareDensity_radius hr0 hw₀ball
    have hcurvw₀ : ρ w₀ ^ 2 ≤ Δ (fun x => Real.log (ρ x)) w₀ := hcurv w₀ hw₀mem hρw₀ne
    have hlampos : 0 < 2 * r / (r ^ 2 - ‖w₀‖ ^ 2) := by positivity
    have hchain : ρ w₀ ^ 2 ≤ (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) ^ 2 := by
      calc ρ w₀ ^ 2 ≤ Δ (fun x => Real.log (ρ x)) w₀ := hcurvw₀
        _ = Δ v w₀ + Δ μ w₀ := by rw [hΔv]; ring
        _ ≤ Δ μ w₀ := by linarith
        _ = _ := hΔμ
    have hρle : ρ w₀ ≤ 2 * r / (r ^ 2 - ‖w₀‖ ^ 2) := by
      nlinarith [hρw₀_pos, hlampos, hchain]
    -- `V w₀ ≤ 1`, hence `V z ≤ 1`, i.e. `ρ z ≤ 2r/(r²−‖z‖²)`.
    have hVw₀_le1 : V w₀ ≤ 1 := by
      rw [hVdef, div_le_one (by positivity)]
      calc ρ w₀ * (r ^ 2 - ‖w₀‖ ^ 2)
            ≤ (2 * r / (r ^ 2 - ‖w₀‖ ^ 2)) * (r ^ 2 - ‖w₀‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hρle hfac_pos.le
        _ = 2 * r := by field_simp
    have hVz_le1 : V z ≤ 1 := le_trans (hw₀max hzcb) hVw₀_le1
    rw [hVdef, div_le_one (by positivity)] at hVz_le1
    rw [le_div_iff₀ hzpos]; exact hVz_le1
  -- Let `r → 1`.
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), ρ z ≤ 2 * r / (r ^ 2 - ‖z‖ ^ 2) := by
    filter_upwards [(eventually_gt_nhds hz).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with r hzr hr1
    exact key r hzr (mem_Iio.mp hr1)
  have hpos1 : (0 : ℝ) < (1 : ℝ) ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hcontat : ContinuousAt (fun r : ℝ => 2 * r / (r ^ 2 - ‖z‖ ^ 2)) 1 := by
    refine ContinuousAt.div ?_ ?_ hpos1.ne'
    · exact continuousAt_const.mul continuousAt_id
    · exact ((continuous_pow 2).continuousAt).sub continuousAt_const
  have htend : Tendsto (fun r : ℝ => 2 * r / (r ^ 2 - ‖z‖ ^ 2)) (𝓝[<] (1 : ℝ))
      (𝓝 (2 * 1 / ((1 : ℝ) ^ 2 - ‖z‖ ^ 2))) := hcontat.tendsto.mono_left nhdsWithin_le_nhds
  have hfin : ρ z ≤ 2 * 1 / ((1 : ℝ) ^ 2 - ‖z‖ ^ 2) := ge_of_tendsto htend hev
  simpa using hfin

open InnerProductSpace in
/-- **Pulled-back density bound (no immersion hypothesis).** For `f` analytic on the unit
disk and omitting `{0,1}`, the pulled-back ultrahyperbolic density
`ρ(z) = (√(1/1000)·σ)(f z)·‖f' z‖` is dominated by the disk Poincaré density,
`ρ z ≤ 2/(1-‖z‖²)`, *including across the critical points* of `f` (where `ρ` vanishes). -/
theorem pullbackDensity_le {f : ℂ → ℂ}
    (hf : ∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) (h1 : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ultraDensityScaled (f z) * ‖deriv f z‖ ≤ 2 / (1 - ‖z‖ ^ 2) := by
  set ρ : ℂ → ℝ := fun w => ultraDensityScaled (f w) * ‖deriv f w‖ with hρdef
  -- Continuity on the disk.
  have hρcont : ContinuousOn ρ (ball (0 : ℂ) 1) := by
    intro w hw
    refine ContinuousAt.continuousWithinAt ?_
    have hσc : ContinuousAt (fun w => ultraDensityScaled (f w)) w :=
      (Real.continuous_exp.continuousAt).comp
        ((contDiffAt_ultraLogDensityScaled (n := 2) (h0 w hw) (h1 w hw)).continuousAt.comp
          (hf w hw).continuousAt)
    exact hσc.mul (hf w hw).deriv.continuousAt.norm
  have hρnonneg : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ ρ w := fun w _ => by
    rw [hρdef]; exact mul_nonneg (ultraDensityScaled_pos _).le (norm_nonneg _)
  -- Where `ρ ≠ 0` (i.e. `f' ≠ 0`), `log ρ = ultraLogDensityScaled ∘ f + log‖f'‖` in a nbhd.
  have hlogeq : ∀ w ∈ ball (0 : ℂ) 1, deriv f w ≠ 0 →
      (fun x => Real.log (ρ x))
        =ᶠ[𝓝 w] fun x => ultraLogDensityScaled (f x) + Real.log ‖deriv f x‖ := by
    intro w hw hderiv0
    have hne : ∀ᶠ x in 𝓝 w, deriv f x ≠ 0 :=
      (hf w hw).deriv.continuousAt.eventually_ne hderiv0
    have hball : ∀ᶠ x in 𝓝 w, x ∈ ball (0 : ℂ) 1 := isOpen_ball.mem_nhds hw
    filter_upwards [hne, hball] with x hx _
    simp only [hρdef, ultraDensityScaled,
      Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.2 hx), Real.log_exp]
  -- `C²` in the logarithm where `ρ ≠ 0`.
  have hC2 : ∀ w ∈ ball (0 : ℂ) 1, ρ w ≠ 0 →
      ContDiffAt ℝ 2 (fun x => Real.log (ρ x)) w := by
    intro w hw hρne
    have hderiv0 : deriv f w ≠ 0 := by
      intro h; rw [hρdef] at hρne; simp [h] at hρne
    have hfR : ContDiffAt ℝ 2 f w := ((hf w hw).contDiffAt).restrict_scalars ℝ
    have hRHS : ContDiffAt ℝ 2 (fun x => ultraLogDensityScaled (f x) + Real.log ‖deriv f x‖) w :=
      ((contDiffAt_ultraLogDensityScaled (h0 w hw) (h1 w hw)).comp w hfR).add
        ((hf w hw).deriv.harmonicAt_log_norm hderiv0).1
    exact hRHS.congr_of_eventuallyEq (hlogeq w hw hderiv0)
  -- Curvature `≤ -1` where `ρ ≠ 0`, via `exp_two_pullback_le_laplacian`.
  have hcurv : ∀ w ∈ ball (0 : ℂ) 1, ρ w ≠ 0 →
      ρ w ^ 2 ≤ Δ (fun x => Real.log (ρ x)) w := by
    intro w hw hρne
    have hderiv0 : deriv f w ≠ 0 := by
      intro h; rw [hρdef] at hρne; simp [h] at hρne
    have hnpos : 0 < ‖deriv f w‖ := norm_pos_iff.2 hderiv0
    have hcurveq : Δ (fun x => Real.log (ρ x)) w
        = Δ (fun x => ultraLogDensityScaled (f x) + Real.log ‖deriv f x‖) w :=
      (laplacian_congr_nhds (hlogeq w hw hderiv0)).eq_of_nhds
    have hexp2u : Real.exp (2 * ultraLogDensityScaled (f w)) = ultraDensityScaled (f w) ^ 2 := by
      rw [ultraDensityScaled, sq, ← Real.exp_add]; ring_nf
    have hexp2n : Real.exp (2 * Real.log ‖deriv f w‖) = ‖deriv f w‖ ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hnpos]
    have hρsq : ρ w ^ 2 = Real.exp (2 * (ultraLogDensityScaled (f w) + Real.log ‖deriv f w‖)) := by
      simp only [hρdef]
      rw [mul_add, Real.exp_add, hexp2u, hexp2n]; ring
    rw [hρsq, hcurveq]
    exact exp_two_pullback_le_laplacian (hf w hw) (h0 w hw) (h1 w hw) hderiv0
  exact ahlfors_schwarz_density hρcont hρnonneg hC2 hcurv hz

/-- **Little Picard theorem.** An entire function `f : ℂ → ℂ` that omits the two values `0`
and `1` is constant.

Proof: feed the pulled-back density `ρ = (√(1/1000)·σ)(f ·)·‖f'‖` into `pullbackDensity_le`
applied to each rescaling `g_R(ζ) = f(a + R·ζ)`.  At `ζ = 0` this gives
`σ(f a)·‖f'(a)‖·R ≤ 2` for **all** `R > 0` and every centre `a`; letting `R → ∞` forces
`f' ≡ 0`, so `f` is constant.  The density form tolerates the critical points that the pure
immersion argument cannot. -/
theorem little_picard {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) (h1 : ∀ z, f z ≠ 1) :
    ∀ a b, f a = f b := by
  suffices hderiv : ∀ a, deriv f a = 0 by
    intro a b; exact is_const_of_deriv_eq_zero hf hderiv a b
  intro a
  by_contra hane
  set A : ℝ := ultraDensityScaled (f a) * ‖deriv f a‖ with hA
  have hApos : 0 < A := mul_pos (ultraDensityScaled_pos _) (norm_pos_iff.2 hane)
  -- Rescaled contraction: `R·A ≤ 2` for all `R > 0`.
  have key : ∀ R : ℝ, 0 < R → R * A ≤ 2 := by
    intro R hR
    have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
    set g : ℂ → ℂ := fun ζ => f (a + (R : ℂ) * ζ) with hg
    have hgderiv : ∀ ζ : ℂ, deriv g ζ = deriv f (a + (R : ℂ) * ζ) * (R : ℂ) := by
      intro ζ
      have hin : HasDerivAt (fun ζ : ℂ => a + (R : ℂ) * ζ) (R : ℂ) ζ := by
        simpa using ((hasDerivAt_id ζ).const_mul (R : ℂ)).const_add a
      have hout : HasDerivAt f (deriv f (a + (R : ℂ) * ζ)) (a + (R : ℂ) * ζ) :=
        (hf (a + (R : ℂ) * ζ)).hasDerivAt
      simpa [hg] using (hout.comp ζ hin).deriv
    have hg_an : ∀ ζ ∈ ball (0 : ℂ) 1, AnalyticAt ℂ g ζ := by
      intro ζ _
      have hfan : AnalyticAt ℂ f (a + (R : ℂ) * ζ) :=
        hf.differentiableOn.analyticAt (IsOpen.mem_nhds isOpen_univ (mem_univ _))
      have hlin : AnalyticAt ℂ (fun ζ : ℂ => a + (R : ℂ) * ζ) ζ :=
        analyticAt_const.add ((analyticAt_const).mul analyticAt_id)
      exact AnalyticAt.comp (g := f) (f := fun ζ : ℂ => a + (R : ℂ) * ζ) hfan hlin
    have hg0 : ∀ ζ ∈ ball (0 : ℂ) 1, g ζ ≠ 0 := fun ζ _ => h0 _
    have hg1 : ∀ ζ ∈ ball (0 : ℂ) 1, g ζ ≠ 1 := fun ζ _ => h1 _
    have hz0 : ‖(0 : ℂ)‖ < 1 := by simp
    have hb := pullbackDensity_le hg_an hg0 hg1 hz0
    have hgz0 : g (0 : ℂ) = f a := by simp [hg]
    have hgderiv0 : deriv g (0 : ℂ) = deriv f a * (R : ℂ) := by rw [hgderiv 0]; simp
    have hnormeq : ‖deriv g (0 : ℂ)‖ = ‖deriv f a‖ * R := by
      rw [hgderiv0]; simp [Complex.norm_real, abs_of_pos hR]
    rw [hgz0, hnormeq] at hb
    have hb2 : ultraDensityScaled (f a) * (‖deriv f a‖ * R) ≤ 2 := by simpa using hb
    calc R * A = ultraDensityScaled (f a) * (‖deriv f a‖ * R) := by rw [hA]; ring
      _ ≤ 2 := hb2
  have hbad := key (3 / A) (by positivity)
  rw [div_mul_cancel₀ 3 (ne_of_gt hApos)] at hbad
  linarith

end MLC.Quadratic
