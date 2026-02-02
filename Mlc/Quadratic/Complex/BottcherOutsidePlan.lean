import Mlc.Quadratic.Complex.BottcherOutsideOutline
import Mlc.Quadratic.Complex.BottcherAnalyticInjective
import Yoccoz.Quadratic.Complex.Green

namespace MLC

open Quadratic Complex Topology Set Filter
open scoped Uniformity

/-!
Plan: eliminate `bottcher_map_inj_on_outside`.

Step 1: Analyticity on the exterior.
  Goal: `AnalyticOnNhd ℂ (bottcher_map c) {‖z‖ > ‖c‖ + 2}`.
  Requires: `outside_disk` (or the open exterior) is contained in `slit_orbit c`.

Step 2: Normalization at infinity.
  Goal: `Tendsto (fun z => bottcher_map c z / z) atInfinity (𝓝 1)`.
  Use: the root sequence, branch coherence on slit, and escape estimates.

Step 3: Derivative nonvanishing on the exterior.
  Goal: `deriv (bottcher_map c) z ≠ 0` on `outside_disk c`.
  Use: analytic order lemma + local injectivity from Step 2.

Step 4: Properness / degree-one argument.
  Goal: global injectivity on `outside_disk c`.
  Use: local injectivity + properness.

Once Steps 1–4 are formalized, remove the axiom
`bottcher_map_inj_on_outside`.
-/

lemma bottcher_map_analytic_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
  bottcher_map_analytic_on_outside_of_slit c hslit

lemma not_injOn_nhds_of_deriv_eq_zero
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hderiv : deriv f z = 0) :
    ∀ s ∈ 𝓝 z, ¬ Set.InjOn f s := by
  have hge :
      (2 : ℕ∞) ≤ analyticOrderAt (fun w => f w - f z) z :=
    analyticOrderAt_sub_ge_two_of_deriv_eq_zero hf hderiv
  exact not_injOn_nhds_of_analyticOrderAt_ge_two hf hge

lemma deriv_ne_zero_of_injOn_nhds
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (s : Set ℂ) (hs : s ∈ 𝓝 z) (hinj : Set.InjOn f s) :
    deriv f z ≠ 0 := by
  intro hzero
  have hnot := not_injOn_nhds_of_deriv_eq_zero hf hzero s hs
  exact hnot hinj

lemma bottcher_ratio_analytic_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (fun z => (Quadratic.bottcher_map c z) / z)
      {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hU : AnalyticOnNhd ℂ (Quadratic.bottcher_map c) U :=
    bottcher_map_analytic_on_outside c hslit
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) U := by
    simpa [U] using (analyticOnNhd_id (𝕜 := ℂ) (s := U))
  have hne : ∀ z ∈ U, z ≠ 0 := by
    intro z hz
    have hz' : ‖z‖ > ‖c‖ + 2 := by simpa [U] using hz
    have hc : 0 < ‖c‖ + 2 := by
      have hc' : 0 ≤ ‖c‖ := by exact norm_nonneg _
      nlinarith
    have : 0 < ‖z‖ := lt_trans hc hz'
    exact (norm_ne_zero_iff).1 (ne_of_gt this)
  simpa [U] using (AnalyticOnNhd.div (f := Quadratic.bottcher_map c) (g := fun z : ℂ => z)
    hU hid hne)

lemma bottcher_normalized_at_infty_iff
    (c : ℂ) :
    bottcher_normalized_at_infty c ↔
      Tendsto (fun z => ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖) atInfinity (𝓝 0) := by
  -- `Tendsto` to `1` in a metric space is equivalent to the norm of the difference tending to `0`.
  simpa [bottcher_normalized_at_infty, dist_eq_norm] using
    (tendsto_iff_dist_tendsto_zero (f := fun z => (Quadratic.bottcher_map c z) / z)
      (a := (1 : ℂ)) (x := atInfinity))

lemma eventually_atInfinity_norm_gt (R : ℝ) :
    ∀ᶠ z in atInfinity, R < ‖z‖ := by
  -- unfold `atInfinity` and use the `atTop` basis.
  dsimp [atInfinity]
  have hR : ∀ᶠ r in (atTop : Filter ℝ), R < r :=
    (Filter.eventually_atTop.2 ⟨R + 1, by intro r hr; linarith⟩)
  -- use the comap characterization
  refine (Filter.eventually_comap).2 ?_
  refine hR.mono ?_
  intro r hr z hz
  simpa [hz] using hr

lemma eventually_atInfinity_mem_outside_open (c : ℂ) :
    ∀ᶠ z in atInfinity, z ∈ {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  have h := eventually_atInfinity_norm_gt (‖c‖ + 2)
  simpa using h

lemma eventually_atInfinity_mem_outside_disk (c : ℂ) :
    ∀ᶠ z in atInfinity, z ∈ outside_disk c := by
  have h := eventually_atInfinity_mem_outside_open c
  refine h.mono ?_
  intro z hz
  exact le_of_lt (by simpa using hz)

-- TODO (Step 2): use the defining root-sequence for `bottcher_map` to show
-- `Tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 1)`.
-- A plausible route:
-- 1) show for each fixed `z` in the basin, the root sequence converges to `bottcher_map c z`;
-- 2) normalize by dividing by `z` and use escape estimates to pass to `atInfinity`;
-- 3) use `eventually_atInfinity_mem_outside_open` to restrict to the exterior where
--    the slit-orbit branch is well-defined.

noncomputable def bottcher_root_seq (c : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((fun w => w ^ 2 + c)^[n] z) ^ ((2 : ℂ) ^ n)⁻¹

lemma bottcher_root_seq_tendsto (c : ℂ) :
    TendstoLocallyUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop
      (Quadratic.basin_of_infinity c) := by
  simpa [bottcher_root_seq, quadratic_map] using (Quadratic.bottcher_seq_converges c)

lemma bottcher_root_seq_tendsto_uniform_on_of_compact
    (c : ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hKbasin : K ⊆ Quadratic.basin_of_infinity c) :
    TendstoUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop K := by
  -- Locally uniform convergence on the basin yields uniform convergence on compacts.
  have hloc :
      TendstoLocallyUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop K :=
    (bottcher_root_seq_tendsto c).mono hKbasin
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (s := K) hK).1 hloc

lemma bottcher_root_seq_tendsto_at (c : ℂ) {z : ℂ}
    (hz : z ∈ Quadratic.basin_of_infinity c) :
    Tendsto (fun n => bottcher_root_seq c n z) atTop (𝓝 (Quadratic.bottcher_map c z)) :=
  (bottcher_root_seq_tendsto c).tendsto_at hz

lemma bottcher_root_seq_ratio_tendsto_at (c : ℂ) {z : ℂ}
    (hz : z ∈ Quadratic.basin_of_infinity c) :
    Tendsto (fun n => (bottcher_root_seq c n z) / z) atTop
      (𝓝 (Quadratic.bottcher_map c z / z)) := by
  have hcont : Continuous (fun w : ℂ => w / z) := by
    simpa [div_eq_mul_inv] using (continuous_id.mul continuous_const)
  exact (hcont.tendsto _).comp (bottcher_root_seq_tendsto_at c hz)

lemma norm_bottcher_root_seq_of_ne_zero
    (c : ℂ) (n : ℕ) (z : ℂ)
    (hzero : (quadratic_map c)^[n] z ≠ 0) :
    ‖bottcher_root_seq c n z‖ =
      ‖(quadratic_map c)^[n] z‖ ^ (((2 : ℂ) ^ n)⁻¹).re /
        Real.exp (Complex.arg ((quadratic_map c)^[n] z) * (((2 : ℂ) ^ n)⁻¹).im) := by
  simpa [bottcher_root_seq] using
    (Complex.norm_cpow_of_ne_zero (z := (quadratic_map c)^[n] z) hzero
      (w := ((2 : ℂ) ^ n)⁻¹))

lemma norm_bottcher_root_seq_eq_rpow_of_ne_zero
    (c : ℂ) (n : ℕ) (z : ℂ)
    (hzero : (quadratic_map c)^[n] z ≠ 0) :
    ‖bottcher_root_seq c n z‖ =
      ‖(quadratic_map c)^[n] z‖ ^ ((1 : ℝ) / (2 : ℝ) ^ n) := by
  have h := norm_bottcher_root_seq_of_ne_zero (c := c) (n := n) (z := z) hzero
  have hreal : ((2 : ℂ) ^ n) = (↑((2 : ℝ) ^ n) : ℂ) := by
    exact (Complex.ofReal_pow (2 : ℝ) n).symm
  have him : (((2 : ℂ) ^ n)⁻¹).im = 0 := by
    set r : ℝ := (2 : ℝ) ^ n
    have h_inv : ((r : ℂ)⁻¹) = ((r⁻¹ : ℝ) : ℂ) := by
      exact (Complex.ofReal_inv r).symm
    calc
      (((2 : ℂ) ^ n)⁻¹).im = ((r : ℂ)⁻¹).im := by
        rw [hreal]
      _ = ((r⁻¹ : ℝ) : ℂ).im := by
        rw [h_inv]
      _ = 0 := by
        exact Complex.ofReal_im _
  have hre : (((2 : ℂ) ^ n)⁻¹).re = (1 : ℝ) / (2 : ℝ) ^ n := by
    set r : ℝ := (2 : ℝ) ^ n
    have h_inv : ((r : ℂ)⁻¹) = ((r⁻¹ : ℝ) : ℂ) := by
      exact (Complex.ofReal_inv r).symm
    calc
      (((2 : ℂ) ^ n)⁻¹).re = ((r : ℂ)⁻¹).re := by
        rw [hreal]
      _ = ((r⁻¹ : ℝ) : ℂ).re := by
        rw [h_inv]
      _ = r⁻¹ := by
        exact Complex.ofReal_re _
      _ = (1 : ℝ) / (2 : ℝ) ^ n := by
        simp [r, one_div]
  simpa [him, hre] using h


lemma bottcher_map_norm_bounds_of_escape (c z : ℂ) (hz : ‖z‖ > escape_bound c) :
    let M : ℝ := 2 * ‖c‖ / (escape_bound c) ^ 2
    Real.exp (-M) * ‖z‖ ≤ ‖Quadratic.bottcher_map c z‖ ∧
      ‖Quadratic.bottcher_map c z‖ ≤ Real.exp M * ‖z‖ := by
  intro M
  have hdist :
      dist (Quadratic.potential_seq c z 0) (Quadratic.green_function c z) ≤ M := by
    simpa [M] using (Quadratic.dist_potential_seq_green_function_le_of_escaping c z 0 hz)
  have hpos : 0 < ‖z‖ := by
    have hR : (2 : ℝ) ≤ escape_bound c := by
      have hR' := Quadratic.escape_bound_ge_R c
      have hR2 := Quadratic.R_ge_two c
      linarith
    linarith
  have hpot :
      Quadratic.potential_seq c z 0 = Real.log ‖z‖ := by
    dsimp [Quadratic.potential_seq]
    have h1 : (1 : ℝ) ≤ ‖z‖ := by
      have hR : (2 : ℝ) ≤ escape_bound c := by
        have hR' := Quadratic.escape_bound_ge_R c
        have hR2 := Quadratic.R_ge_two c
        linarith
      linarith
    have hmax : max 1 ‖z‖ = ‖z‖ := max_eq_right h1
    simp [hmax]
  have hdist' :
      |Real.log ‖z‖ - Quadratic.green_function c z| ≤ M := by
    simpa [hpot, Real.dist_eq, abs_sub_comm] using hdist
  have hle : Real.log ‖z‖ - M ≤ Quadratic.green_function c z ∧
      Quadratic.green_function c z ≤ Real.log ‖z‖ + M := by
    have h := abs_sub_le_iff.mp hdist'
    constructor <;> linarith
  have hnorm : ‖Quadratic.bottcher_map c z‖ =
      Real.exp (Quadratic.green_function c z) :=
    Quadratic.norm_bottcher_eq_exp_green c z
  have hlow :
      Real.exp (Real.log ‖z‖ - M) ≤ Real.exp (Quadratic.green_function c z) := by
    exact Real.exp_le_exp.mpr hle.1
  have hhigh :
      Real.exp (Quadratic.green_function c z) ≤ Real.exp (Real.log ‖z‖ + M) := by
    exact Real.exp_le_exp.mpr hle.2
  have hlow' : Real.exp (Real.log ‖z‖ - M) = Real.exp (-M) * ‖z‖ := by
    calc
      Real.exp (Real.log ‖z‖ - M)
          = Real.exp (Real.log ‖z‖ + (-M)) := by ring_nf
      _ = Real.exp (Real.log ‖z‖) * Real.exp (-M) := by
            simp [Real.exp_add]
      _ = ‖z‖ * Real.exp (-M) := by
            simp [Real.exp_log hpos]
      _ = Real.exp (-M) * ‖z‖ := by
            ring
  have hhigh' : Real.exp (Real.log ‖z‖ + M) = Real.exp M * ‖z‖ := by
    calc
      Real.exp (Real.log ‖z‖ + M)
          = Real.exp (Real.log ‖z‖) * Real.exp M := by
            simp [Real.exp_add]
      _ = ‖z‖ * Real.exp M := by
            simp [Real.exp_log hpos]
      _ = Real.exp M * ‖z‖ := by
            ring
  constructor
  · have : Real.exp (-M) * ‖z‖ ≤ Real.exp (Quadratic.green_function c z) := by
      simpa [hlow'] using hlow
    simpa [hnorm] using this
  · have : Real.exp (Quadratic.green_function c z) ≤ Real.exp M * ‖z‖ := by
      simpa [hhigh'] using hhigh
    simpa [hnorm] using this

-- Step 2 (route 2): reduce normalization at infinity to a root-sequence estimate.
lemma bottcher_normalized_at_infty_of_root_seq
    (c : ℂ) (N : ℕ)
    (hroot : Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)))
    (herror : Tendsto (fun z => (Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z)
      atInfinity (𝓝 (0 : ℂ))) :
    bottcher_normalized_at_infty c := by
  dsimp [bottcher_normalized_at_infty]
  have hsum :
      Tendsto
        (fun z =>
          bottcher_root_seq c N z / z +
            (Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z)
        atInfinity (𝓝 ((1 : ℂ) + 0)) := by
    exact hroot.add herror
  have hsplit :
      (fun z => (Quadratic.bottcher_map c z) / z) =
        fun z =>
          bottcher_root_seq c N z / z +
            (Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z := by
    funext z
    -- Combine the fractions using `add_div` and simplify the numerator.
    have hnum :
        bottcher_root_seq c N z + (Quadratic.bottcher_map c z - bottcher_root_seq c N z) =
          Quadratic.bottcher_map c z := by
      calc
        bottcher_root_seq c N z + (Quadratic.bottcher_map c z - bottcher_root_seq c N z)
            = Quadratic.bottcher_map c z + bottcher_root_seq c N z - bottcher_root_seq c N z := by
                simp [sub_eq_add_neg, add_left_comm, add_comm]
        _ = Quadratic.bottcher_map c z := by
                simp
    calc
      (Quadratic.bottcher_map c z) / z
          = (bottcher_root_seq c N z +
              (Quadratic.bottcher_map c z - bottcher_root_seq c N z)) / z := by
              simp [hnum]
      _ =
          bottcher_root_seq c N z / z +
            (Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z := by
              simpa using
                (add_div (bottcher_root_seq c N z)
                  (Quadratic.bottcher_map c z - bottcher_root_seq c N z) z)
  simpa [hsplit] using hsum

lemma bottcher_root_seq_error_tendsto
    (c : ℂ) (N : ℕ)
    (hbound :
      ∀ ε > 0, ∀ᶠ z in atInfinity,
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖) :
    Tendsto (fun z => (Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z)
      atInfinity (𝓝 (0 : ℂ)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have hgoal :
      Tendsto
        (fun z => ‖(Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z‖)
        atInfinity (𝓝 (0 : ℝ)) := by
    refine (tendsto_order.2 ?_)
    constructor
    · intro a ha
      have hnonneg : ∀ z,
          0 ≤ ‖(Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z‖ := by
        intro z
        exact norm_nonneg _
      exact Filter.Eventually.of_forall (fun z => lt_of_lt_of_le ha (hnonneg z))
    · intro a ha
      have ha' : 0 < a / 2 := by
        nlinarith
      have hbound' := hbound (a / 2) ha'
      have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
        (eventually_atInfinity_norm_gt (0 : ℝ))
      refine (hbound'.and hpos).mono ?_
      intro z hz
      rcases hz with ⟨hbd, hzpos⟩
      have hnorm :
          ‖(Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z‖ =
            ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ / ‖z‖ := by
        exact norm_div (Quadratic.bottcher_map c z - bottcher_root_seq c N z) z
      have hle :
          ‖(Quadratic.bottcher_map c z - bottcher_root_seq c N z) / z‖ ≤ a / 2 := by
        have hle' :
            ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ / ‖z‖ ≤ a / 2 := by
          have : ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ (a / 2) * ‖z‖ :=
            hbd
          exact (div_le_iff₀ hzpos).2 (by simpa [mul_comm] using this)
        simpa [hnorm] using hle'
      have hlt : a / 2 < a := by
        nlinarith
      exact lt_of_le_of_lt hle hlt
  simpa using hgoal

lemma bottcher_root_seq_error_bound_of_exterior
    (c : ℂ) (N : ℕ)
    (hR :
      ∀ ε > 0, ∃ R, ∀ z, R ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖) :
    ∀ ε > 0, ∀ᶠ z in atInfinity,
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖ := by
  intro ε hε
  rcases hR ε hε with ⟨R, hR'⟩
  have hlarge : ∀ᶠ z in atInfinity, R < ‖z‖ :=
    eventually_atInfinity_norm_gt R
  refine hlarge.mono ?_
  intro z hz
  exact hR' z (le_of_lt hz)

lemma bottcher_root_seq_error_bound_of_uniform_on
    (c : ℂ) (N : ℕ)
    (hU :
      ∀ ε > 0, ∃ R, ∀ z, R ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * R) :
    ∀ ε > 0, ∃ R, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖ := by
  intro ε hε
  rcases hU ε hε with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro z hz
  have hle : ε * R ≤ ε * ‖z‖ :=
    mul_le_mul_of_nonneg_left hz (le_of_lt hε)
  exact (hR z hz).trans hle

lemma bottcher_root_seq_error_bound_of_tendstoUniformlyOn
    (c : ℂ) (R : ℝ)
    (hU : TendstoUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop
      {z : ℂ | R ≤ ‖z‖}) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε := by
  intro ε hε
  let u : Set (ℂ × ℂ) := {p | dist p.1 p.2 < ε}
  have hu : u ∈ 𝓤 ℂ := Metric.mem_uniformity_dist.mpr ⟨ε, hε, by simp [u]⟩
  have hU' := hU u hu
  rcases (Filter.eventually_atTop.1 hU') with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn z hz
  have hmem : (Quadratic.bottcher_map c z, bottcher_root_seq c n z) ∈ u :=
    hN n hn z hz
  have hdist : dist (Quadratic.bottcher_map c z) (bottcher_root_seq c n z) < ε := by
    simpa [u] using hmem
  have hle : dist (Quadratic.bottcher_map c z) (bottcher_root_seq c n z) ≤ ε :=
    le_of_lt hdist
  simpa [dist_eq] using hle

lemma uniform_bound_of_tendstoUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {s : Set ℂ}
    (hU : TendstoUniformlyOn F f atTop s) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, z ∈ s → ‖f z - F n z‖ ≤ ε := by
  intro ε hε
  let u : Set (ℂ × ℂ) := {p | dist p.1 p.2 < ε}
  have hu : u ∈ 𝓤 ℂ := Metric.mem_uniformity_dist.mpr ⟨ε, hε, by simp [u]⟩
  have hU' := hU u hu
  rcases (Filter.eventually_atTop.1 hU') with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn z hz
  have hmem : (f z, F n z) ∈ u := hN n hn z hz
  have hdist : dist (f z) (F n z) < ε := by
    simpa [u] using hmem
  have hle : dist (f z) (F n z) ≤ ε :=
    le_of_lt hdist
  simpa [dist_eq] using hle

def exterior_annulus (R S : ℝ) : Set ℂ :=
  {z : ℂ | R ≤ ‖z‖ ∧ ‖z‖ ≤ S}

lemma isCompact_exterior_annulus (R S : ℝ) : IsCompact (exterior_annulus R S) := by
  have hclosed1 : IsClosed {z : ℂ | R ≤ ‖z‖} := by
    simpa using (isClosed_le continuous_const continuous_norm)
  have hclosed2 : IsClosed {z : ℂ | ‖z‖ ≤ S} := by
    simpa using (isClosed_le continuous_norm continuous_const)
  have hclosed : IsClosed (exterior_annulus R S) := by
    simpa [exterior_annulus] using hclosed1.inter hclosed2
  have hsubset : exterior_annulus R S ⊆ Metric.closedBall (0 : ℂ) S := by
    intro z hz
    have hz' : ‖z‖ ≤ S := hz.2
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  exact (isCompact_closedBall (0 : ℂ) S).of_isClosed_subset hclosed hsubset

lemma exterior_annulus_subset_outside_disk (c : ℂ) {R S : ℝ}
    (hR : ‖c‖ + 2 ≤ R) :
    exterior_annulus R S ⊆ outside_disk c := by
  intro z hz
  have hz' : ‖z‖ ≥ R := hz.1
  exact le_trans hR hz'

lemma bottcher_root_seq_tendsto_uniform_on_annulus_of_large_R
    (c : ℂ) {R S : ℝ} (hR : ‖c‖ + 2 ≤ R) :
    TendstoUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop
      (exterior_annulus R S) := by
  have hK : IsCompact (exterior_annulus R S) := isCompact_exterior_annulus R S
  have hKbasin : exterior_annulus R S ⊆ Quadratic.basin_of_infinity c := by
    intro z hz
    have hz_out : z ∈ outside_disk c :=
      exterior_annulus_subset_outside_disk c (S := S) hR hz
    exact outside_disk_subset_quadratic_basin c hz_out
  exact bottcher_root_seq_tendsto_uniform_on_of_compact c _ hK hKbasin

lemma bottcher_root_seq_error_bound_of_annulus_and_tail
    (c : ℂ) (R : ℝ)
    (hannulus :
      ∀ S, R ≤ S →
        TendstoUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop
          (exterior_annulus R S))
    (htail :
      ∀ ε > 0, ∃ S ≥ R, ∀ n z, S ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε := by
  intro ε hε
  rcases htail ε hε with ⟨S, hSR, htail'⟩
  have hann := hannulus S hSR
  rcases uniform_bound_of_tendstoUniformlyOn (F := bottcher_root_seq c)
    (f := Quadratic.bottcher_map c) (s := exterior_annulus R S) hann ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn z hz
  by_cases hzs : ‖z‖ ≤ S
  · have hz' : z ∈ exterior_annulus R S := ⟨hz, hzs⟩
    have h := hN n hn z hz'
    exact h
  · have hzs' : S ≤ ‖z‖ := le_of_not_ge hzs
    exact htail' n z hzs'

lemma bottcher_root_seq_error_bound_of_large_R
    (c : ℂ) (R : ℝ) (hR : ‖c‖ + 2 ≤ R)
    (htail :
      ∀ ε > 0, ∃ S ≥ R, ∀ n z, S ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε := by
  refine bottcher_root_seq_error_bound_of_annulus_and_tail c R ?_ htail
  intro S hRS
  have hR' : ‖c‖ + 2 ≤ R := hR
  exact bottcher_root_seq_tendsto_uniform_on_annulus_of_large_R c (R := R) (S := S) hR'

lemma bottcher_normalized_at_infty_of_root_seq_bound
    (c : ℂ) (N : ℕ)
    (hroot : Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)))
    (hbound :
      ∀ ε > 0, ∀ᶠ z in atInfinity,
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖) :
    bottcher_normalized_at_infty c := by
  refine bottcher_normalized_at_infty_of_root_seq c N hroot ?_
  exact bottcher_root_seq_error_tendsto c N hbound

lemma bottcher_normalized_at_infty_of_large_R
    (c : ℂ) (R : ℝ) (hR : ‖c‖ + 2 ≤ R) (N : ℕ)
    (hroot : Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)))
    (htail :
      ∀ ε > 0, ∃ S ≥ R, ∀ n z, S ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε) :
    bottcher_normalized_at_infty c := by
  have hbound' :
      ∀ ε > 0, ∀ᶠ z in atInfinity,
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖ := by
    intro ε hε
    rcases htail ε hε with ⟨S, hSR, htail'⟩
    have hlarge : ∀ᶠ z in atInfinity, S < ‖z‖ :=
      eventually_atInfinity_norm_gt S
    refine hlarge.mono ?_
    intro z hz
    have habs : ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε :=
      htail' N z (le_of_lt hz)
    have hle : ε ≤ ε * ‖z‖ := by
      have hR1 : (1 : ℝ) ≤ R := by
        have hcn : (0 : ℝ) ≤ ‖c‖ := by exact norm_nonneg _
        nlinarith
      have hzge : 1 ≤ ‖z‖ := le_trans (le_trans hR1 hSR) (le_of_lt hz)
      nlinarith
    exact habs.trans hle
  exact bottcher_normalized_at_infty_of_root_seq_bound c N hroot hbound'

def bottcher_tail_bound (c : ℂ) (R : ℝ) : Prop :=
  ∀ ε > 0, ∃ S ≥ R, ∀ n z, S ≤ ‖z‖ →
    ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε

theorem bottcher_normalized_at_infty_of_tail_bound
    (c : ℂ) (R : ℝ) (hR : ‖c‖ + 2 ≤ R) (N : ℕ)
    (hroot : Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)))
    (htail : bottcher_tail_bound c R) :
    bottcher_normalized_at_infty c :=
  bottcher_normalized_at_infty_of_large_R c R hR N hroot htail

lemma outside_open_subset_outside_disk (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ outside_disk c := by
  intro z hz
  have hz' : ‖z‖ > ‖c‖ + 2 := by simpa using hz
  exact le_of_lt hz'

lemma bottcher_map_deriv_ne_zero_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hinj : Set.InjOn (Quadratic.bottcher_map c) (outside_disk c)) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  intro z hz
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  have hUnhds : U ∈ 𝓝 z := hUopen.mem_nhds (by simpa [U] using hz)
  have hf : AnalyticAt ℂ (Quadratic.bottcher_map c) z :=
    (bottcher_map_analytic_on_outside c hslit) z (by simpa [U] using hz)
  have hinjU : Set.InjOn (Quadratic.bottcher_map c) U :=
    hinj.mono (by simpa [U] using outside_open_subset_outside_disk c)
  exact deriv_ne_zero_of_injOn_nhds hf U hUnhds hinjU

-- The open exterior `{‖z‖ > ‖c‖ + 2}` is the natural domain for Step 1.
-- Extending analyticity to the closed `outside_disk` would need boundary control.

def slitPlaneRot (θ : ℝ) : Set ℂ :=
  {z | z * Complex.exp (-Complex.I * θ) ∈ Complex.slitPlane}

lemma isOpen_slitPlaneRot (θ : ℝ) : IsOpen (slitPlaneRot θ) := by
  have hcont : Continuous (fun z : ℂ => z * Complex.exp (-Complex.I * θ)) := by
    simpa using (continuous_id.mul continuous_const)
  exact (isOpen_slitPlane.preimage hcont)

def slit_orbit_rot (c : ℂ) (θ : ℝ) : Set ℂ :=
  {z | ∀ n, (quadratic_map c)^[n] z ∈ slitPlaneRot θ}

lemma slitPlaneRot_zero : slitPlaneRot 0 = Complex.slitPlane := by
  ext z
  simp [slitPlaneRot]

lemma slit_orbit_rot_zero (c : ℂ) : slit_orbit_rot c 0 = slit_orbit c := by
  ext z
  simp [slit_orbit_rot, slit_orbit, slitPlaneRot_zero]

lemma slit_orbit_rot_iff (c : ℂ) (θ : ℝ) (z : ℂ) :
    z ∈ slit_orbit_rot c θ ↔
      ∀ n, (quadratic_map c)^[n] z * Complex.exp (-Complex.I * θ) ∈ Complex.slitPlane := by
  rfl

lemma quadratic_map_rotate (c : ℂ) (θ : ℝ) (z : ℂ) :
    quadratic_map c (z * Complex.exp (Complex.I * θ)) =
      (quadratic_map (c * Complex.exp (-Complex.I * θ * 2)) z) *
        Complex.exp (Complex.I * θ * 2) := by
  -- Algebraic conjugation identity under rotation.
  have hexp :
      (Complex.exp (Complex.I * θ)) ^ 2 = Complex.exp (Complex.I * θ * 2) := by
    -- `exp (2 * x) = exp x ^ 2`
    have h := (Complex.exp_nat_mul (Complex.I * θ) 2).symm
    -- rewrite `2 * (I*θ)` as `(I*θ) * 2`
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  calc
    quadratic_map c (z * Complex.exp (Complex.I * θ))
        = (z * Complex.exp (Complex.I * θ)) ^ 2 + c := by rfl
    _ = z ^ 2 * (Complex.exp (Complex.I * θ)) ^ 2 + c := by
          simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
    _ = z ^ 2 * Complex.exp (Complex.I * θ * 2) + c := by
          simp [hexp]
    _ = z ^ 2 * Complex.exp (Complex.I * θ * 2) +
        Complex.exp (Complex.I * θ * 2) * c * Complex.exp (-Complex.I * θ * 2) := by
          have hmul :
              Complex.exp (Complex.I * θ * 2) * Complex.exp (-(Complex.I * θ * 2)) = 1 := by
            rw [← Complex.exp_add]
            simp
          -- insert `1 = exp(...) * exp(-...)` next to `c`
          calc
            z ^ 2 * Complex.exp (Complex.I * θ * 2) + c
                = z ^ 2 * Complex.exp (Complex.I * θ * 2) +
                    c * (Complex.exp (Complex.I * θ * 2) * Complex.exp (-(Complex.I * θ * 2))) := by
                      simp [hmul]
            _ = z ^ 2 * Complex.exp (Complex.I * θ * 2) +
                Complex.exp (Complex.I * θ * 2) * c * Complex.exp (-Complex.I * θ * 2) := by
                  ring_nf
    _ = (quadratic_map (c * Complex.exp (-Complex.I * θ * 2)) z) *
        Complex.exp (Complex.I * θ * 2) := by
          simp [quadratic_map, mul_add, mul_assoc, mul_comm, mul_left_comm]

lemma quadratic_map_rotate_only_trivial
    (c c' : ℂ) (θ : ℝ)
    (h : ∀ z, quadratic_map c (z * Complex.exp (Complex.I * θ)) =
      (quadratic_map c' z) * Complex.exp (Complex.I * θ)) :
    Complex.exp (Complex.I * θ) = 1 ∧ c' = c := by
  have h0 := h 0
  have h1 := h 1
  set e : ℂ := Complex.exp (Complex.I * θ)
  have hc : c = c' * e := by
    simpa [quadratic_map, e] using h0
  have h1' : e ^ 2 + c' * e = e + c' * e := by
    have h1'' : e ^ 2 + c = e * (1 + c') := by
      simpa [quadratic_map, e, pow_two, mul_assoc, mul_comm, mul_left_comm] using h1
    have h1''' : e ^ 2 + c = e + c' * e := by
      simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using h1''
    simpa [hc, add_assoc, add_left_comm, add_comm] using h1'''
  have hθ : e ^ 2 = e := by
    have h1'' : c' * e + e ^ 2 = c' * e + e := by
      simpa [add_comm, add_left_comm, add_assoc] using h1'
    exact add_left_cancel h1''
  have hθ' : e = 1 := by
    have h : e * (e - 1) = 0 := by
      calc
        e * (e - 1) = e ^ 2 - e := by ring
        _ = 0 := by simp [hθ]
    have hne : e ≠ 0 := by
      dsimp [e]
      exact Complex.exp_ne_zero (Complex.I * θ)
    have : e - 1 = 0 := (mul_eq_zero.mp h).resolve_left hne
    exact sub_eq_zero.mp this
  have hc' : c' = c := by
    have hc'' : c = c' := by
      simpa [hθ'] using hc
    exact hc''.symm
  exact ⟨hθ', hc'⟩

lemma slit_orbit_rot_forward (c : ℂ) (θ : ℝ) :
    MapsTo (quadratic_map c) (slit_orbit_rot c θ) (slit_orbit_rot c θ) := by
  intro z hz n
  -- unfold `slit_orbit_rot` and shift the index
  simpa [Function.iterate_succ_apply] using (hz (n + 1))

def local_slit (z₀ : ℂ) (ε : ℝ) : Set ℂ :=
  {z | dist z z₀ < ε} ∩ {z | z - z₀ ∈ Complex.slitPlane}

lemma local_slit_subset_slitPlane (z₀ : ℂ) (ε : ℝ) :
    local_slit z₀ ε ⊆ {z | z - z₀ ∈ Complex.slitPlane} := by
  intro z hz
  exact hz.2

lemma local_slit_isOpen (z₀ : ℂ) (ε : ℝ) : IsOpen (local_slit z₀ ε) := by
  have hball : IsOpen {z : ℂ | dist z z₀ < ε} :=
    Metric.isOpen_ball
  have hslit : IsOpen {z : ℂ | z - z₀ ∈ Complex.slitPlane} := by
    have hcont : Continuous (fun z : ℂ => z - z₀) := by
      simpa using (continuous_id.sub continuous_const)
    exact (isOpen_slitPlane.preimage hcont)
  exact hball.inter hslit

-- TODO: for each exterior point z₀, choose ε>0 with
-- `local_slit z₀ ε ⊆ slit_orbit c` (avoid the branch cut locally).

lemma bottcher_map_analytic_on_local_slit
    (c z₀ : ℂ) (ε : ℝ)
    (hslit : local_slit z₀ ε ⊆ slit_orbit c)
    (hbasin : local_slit z₀ ε ⊆ Quadratic.basin_of_infinity c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) (local_slit z₀ ε) := by
  have hopen : IsOpen (local_slit z₀ ε) := local_slit_isOpen z₀ ε
  exact bottcher_map_analyticOnNhd_open c (local_slit z₀ ε) hopen hslit hbasin

lemma isOpen_preimage_slitPlane_iter (c : ℂ) (n : ℕ) :
    IsOpen {z : ℂ | (quadratic_map c)^[n] z ∈ Complex.slitPlane} := by
  have hcont : Continuous (fun z : ℂ => (quadratic_map c)^[n] z) :=
    (continuous_quadratic_map c).iterate n
  exact (isOpen_slitPlane.preimage hcont)

lemma exists_ball_subset_slit_orbit_prefix
    (c z₀ : ℂ) (N : ℕ) (hz₀ : z₀ ∈ slit_orbit c) :
    ∃ ε > 0, ∀ z, dist z z₀ < ε →
      ∀ n ≤ N, (quadratic_map c)^[n] z ∈ Complex.slitPlane := by
  induction N with
  | zero =>
      have hmem : z₀ ∈ {z : ℂ | z ∈ Complex.slitPlane} := hz₀ 0
      have hnhds : {z : ℂ | z ∈ Complex.slitPlane} ∈ 𝓝 z₀ :=
        isOpen_slitPlane.mem_nhds hmem
      rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, εpos, hball⟩
      refine ⟨ε, εpos, ?_⟩
      intro z hz n hn
      have hn' : n = 0 := Nat.le_zero.mp hn
      subst hn'
      exact hball hz
  | succ N ih =>
      rcases ih with ⟨ε, εpos, hε⟩
      have hmem : z₀ ∈ {z : ℂ | (quadratic_map c)^[N + 1] z ∈ Complex.slitPlane} :=
        hz₀ (N + 1)
      have hnhds :
          {z : ℂ | (quadratic_map c)^[N + 1] z ∈ Complex.slitPlane} ∈ 𝓝 z₀ :=
        (isOpen_preimage_slitPlane_iter c (N + 1)).mem_nhds hmem
      rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε2, ε2pos, hball2⟩
      let ε' := min ε ε2
      have ε'pos : 0 < ε' := lt_min εpos ε2pos
      refine ⟨ε', ε'pos, ?_⟩
      intro z hz n hn
      have hzε : dist z z₀ < ε := lt_of_lt_of_le hz (min_le_left _ _)
      have hzε2 : dist z z₀ < ε2 := lt_of_lt_of_le hz (min_le_right _ _)
      have hle : n ≤ N ∨ n = N + 1 := by
        exact (lt_or_eq_of_le hn).elim (fun hlt => Or.inl (Nat.le_of_lt_succ hlt)) Or.inr
      cases hle with
      | inl hle' =>
          exact hε z hzε n hle'
      | inr hEq =>
          subst hEq
          exact hball2 hzε2

-- TODO: iterate-level conjugacy under rotation.
-- This should follow from `quadratic_map_rotate` by induction, with a corrected
-- expression for the parameter after rotation.

-- TODO: relate rotated slit orbits to the principal slit orbit.
-- The naive statement `z * exp(-I*θ) ∈ slit_orbit c` requires a conjugacy
-- argument on iterates, which will use `quadratic_map_rotate`.

lemma bottcher_map_analytic_on_outside_of_slit_rot
    (c : ℂ) (θ : ℝ)
    (_hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit_rot c θ)
    (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
  bottcher_map_analytic_on_outside c hslit
end MLC
