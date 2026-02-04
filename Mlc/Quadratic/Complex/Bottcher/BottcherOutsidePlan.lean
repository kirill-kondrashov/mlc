import Mlc.Quadratic.Complex.Bottcher.BottcherOutsideOutline
import Mlc.Quadratic.Complex.Bottcher.BottcherAnalyticInjective
import Mlc.Quadratic.Complex.Bottcher.BottcherCpowSlit
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Complex.Liouville

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

lemma injOn_nhds_of_hasStrictDerivAt
    {f : ℂ → ℂ} {f' z : ℂ} (hf : HasStrictDerivAt f f' z) (hf' : f' ≠ 0) :
    ∃ s ∈ 𝓝 z, Set.InjOn f s := by
  let g := HasStrictDerivAt.localInverse f f' z hf hf'
  let s : Set ℂ := {x | g (f x) = x}
  have hs : s ∈ 𝓝 z :=
    (HasStrictDerivAt.eventually_left_inverse (f := f) (f' := f') (a := z) hf hf')
  refine ⟨s, hs, ?_⟩
  intro x hx y hy hxy
  have hx' : g (f x) = x := by
    simp [s] at hx
    exact hx
  have hy' : g (f y) = y := by
    simp [s] at hy
    exact hy
  calc
    x = g (f x) := by symm; exact hx'
    _ = g (f y) := by simp [hxy]
    _ = y := hy'

lemma injOn_nhds_of_analyticAt
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hderiv : deriv f z ≠ 0) :
    ∃ s ∈ 𝓝 z, Set.InjOn f s := by
  have hf' : HasStrictDerivAt f (deriv f z) z := hf.hasStrictDerivAt
  exact injOn_nhds_of_hasStrictDerivAt (f := f) (f' := deriv f z) (z := z) hf' hderiv

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

lemma tendsto_atInfinity_norm_atTop :
    Tendsto (fun z : ℂ => ‖z‖) atInfinity atTop := by
  simpa [atInfinity] using
    (tendsto_comap : Tendsto (fun z : ℂ => ‖z‖) (Filter.comap (fun z : ℂ => ‖z‖) atTop) atTop)

lemma tendsto_atInfinity_norm_pow_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => ‖z‖ ^ k) atInfinity atTop := by
  refine tendsto_atTop.2 ?_
  intro R
  by_cases hR : R ≤ 0
  · exact Filter.Eventually.of_forall (fun z => le_trans hR (pow_nonneg (norm_nonneg _) _))
  · have hR' : 0 < R := lt_of_not_ge hR
    have hlarge : ∀ᶠ z in atInfinity, max 1 R < ‖z‖ :=
      eventually_atInfinity_norm_gt (max 1 R)
    refine hlarge.mono ?_
    intro z hz
    have hz1 : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz)
    have hzR : R ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨n, rfl⟩
    have hpow1 : (1 : ℝ) ≤ ‖z‖ ^ n := by
      exact one_le_pow₀ hz1
    have hpow : ‖z‖ ≤ ‖z‖ ^ (n + 1) := by
      have hmul := mul_le_mul_of_nonneg_right hpow1 (norm_nonneg z)
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact le_trans hzR hpow

lemma tendsto_atInfinity_norm_pow_atTop' (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => ‖z ^ k‖) atInfinity atTop := by
  simpa [norm_pow] using (tendsto_atInfinity_norm_pow_atTop k hk)

lemma tendsto_atInfinity_inv_pow_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => (z ^ k)⁻¹) atInfinity (𝓝 (0 : ℂ)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have hpow : Tendsto (fun z : ℂ => ‖z ^ k‖) atInfinity atTop :=
    tendsto_atInfinity_norm_pow_atTop' k hk
  have hpow_inv : Tendsto (fun z : ℂ => (‖z ^ k‖)⁻¹) atInfinity (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow
  simpa [norm_inv] using hpow_inv

lemma tendsto_atInfinity_const_div_pow_zero (c : ℂ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => c / z ^ k) atInfinity (𝓝 (0 : ℂ)) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_atInfinity_inv_pow_zero (k := k) hk))

lemma tendsto_quadratic_iter_div_pow_atInfinity (c : ℂ) :
    ∀ N, Tendsto (fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)) atInfinity (𝓝 (1 : ℂ))
  | 0 => by
      have hne : ∀ᶠ z in atInfinity, z ≠ 0 := by
        have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
          (eventually_atInfinity_norm_gt (0 : ℝ))
        exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
      have hconst : Tendsto (fun _ : ℂ => (1 : ℂ)) atInfinity (𝓝 (1 : ℂ)) :=
        tendsto_const_nhds
      refine (tendsto_congr' ?_).1 hconst
      refine hne.mono ?_
      intro z hz
      simp [hz]
  | N + 1 => by
      have hN : Tendsto (fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)) atInfinity (𝓝 (1 : ℂ)) :=
        tendsto_quadratic_iter_div_pow_atInfinity c N
      let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
      have hsq : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
        have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
        have h := (hcont.tendsto (1 : ℂ)).comp hN
        simpa using h
      have hsmall : Tendsto (fun z => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
        have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
        exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
      have hsum :
          Tendsto
            (fun z => (g z) ^ 2 + c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (1 : ℂ)) := by
        simpa using hsq.add hsmall
      refine (tendsto_congr' ?_).1 hsum
      refine Filter.Eventually.of_forall ?_
      intro z
      have hpow : z ^ (2 ^ (N + 1)) = (z ^ (2 ^ N)) ^ 2 := by
        simp [pow_succ, pow_mul]
      have hdiv :
          ((quadratic_map c)^[N] z) ^ 2 / z ^ (2 ^ (N + 1)) =
            (g z) ^ 2 := by
        calc
          ((quadratic_map c)^[N] z) ^ 2 / z ^ (2 ^ (N + 1))
              = ((quadratic_map c)^[N] z) ^ 2 / (z ^ (2 ^ N)) ^ 2 := by
                  simp [hpow]
          _ = (g z) ^ 2 := by
                  simpa [g, pow_two] using
                    (div_pow (a := (quadratic_map c)^[N] z) (b := z ^ (2 ^ N)) (n := 2)).symm
      simp [quadratic_map, Function.iterate_succ_apply', add_div, hdiv, g]


-- TODO (Step 2): use the defining root-sequence for `bottcher_map` to show
-- `Tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 1)`.
-- A plausible route:
-- 1) show for each fixed `z` in the basin, the root sequence converges to `bottcher_map c z`;
-- 2) normalize by dividing by `z` and use escape estimates to pass to `atInfinity`;
-- 3) use `eventually_atInfinity_mem_outside_open` to restrict to the exterior where
--    the slit-orbit branch is well-defined.

noncomputable def bottcher_root_seq (c : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((fun w => w ^ 2 + c)^[n] z) ^ ((2 : ℂ) ^ n)⁻¹

lemma bottcher_root_seq_zero (c : ℂ) (z : ℂ) :
    bottcher_root_seq c 0 z = z := by
  simp [bottcher_root_seq]

lemma bottcher_root_seq_succ (c : ℂ) (N : ℕ) (z : ℂ) :
    bottcher_root_seq c (N + 1) z =
      (((fun w => w ^ 2 + c)^[N] z) ^ 2 + c) ^ ((2 : ℂ) ^ (N + 1))⁻¹ := by
  simp [bottcher_root_seq, Function.iterate_succ_apply']

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

lemma bottcher_root_seq_ratio_tendsto_atInfinity_one_add
    (c : ℂ) (N : ℕ) :
    Tendsto (fun z => (1 + c / z ^ (2 ^ N)) ^ ((2 : ℂ) ^ N)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
  have hsmall : Tendsto (fun z : ℂ => c / z ^ (2 ^ N)) atInfinity (𝓝 (0 : ℂ)) := by
    have hk : 0 < 2 ^ N := pow_pos (by norm_num : (0 : ℕ) < 2) _
    exact tendsto_atInfinity_const_div_pow_zero c (2 ^ N) hk
  have hsum : Tendsto (fun z : ℂ => (1 : ℂ) + c / z ^ (2 ^ N)) atInfinity (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.add hsmall)
  exact tendsto_cpow_const_of_tendsto_one (f := fun z : ℂ => (1 : ℂ) + c / z ^ (2 ^ N))
    (a := ((2 : ℂ) ^ N)⁻¹) hsum

lemma eventually_atInfinity_norm_div_pow_lt_one
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity, ‖c / z ^ (2 ^ N)‖ < (1 : ℝ) := by
  have hsmall : Tendsto (fun z : ℂ => c / z ^ (2 ^ N)) atInfinity (𝓝 (0 : ℂ)) := by
    have hk : 0 < 2 ^ N := pow_pos (by norm_num : (0 : ℕ) < 2) _
    exact tendsto_atInfinity_const_div_pow_zero c (2 ^ N) hk
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  have h := tendsto_def.1 hsmall _ hball
  simpa [Metric.ball, Set.mem_setOf_eq, dist_eq_norm] using h

lemma eventually_atInfinity_one_add_mem_slitPlane
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity, (1 + c / z ^ (2 ^ N)) ∈ Complex.slitPlane := by
  have hlt := eventually_atInfinity_norm_div_pow_lt_one c N
  refine hlt.mono ?_
  intro z hz
  have hlt' : ‖(1 + c / z ^ (2 ^ N)) - (1 : ℂ)‖ < 1 := by
    simpa using hz
  exact mem_slitPlane_of_norm_sub_one_lt_one hlt'

lemma eventually_atInfinity_abs_arg_lt_pi_div_two_one_add
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity, |Complex.arg (1 + c / z ^ (2 ^ N))| < Real.pi / 2 := by
  have hlt := eventually_atInfinity_norm_div_pow_lt_one c N
  refine hlt.mono ?_
  intro z hz
  have hlt' : ‖(1 + c / z ^ (2 ^ N)) - (1 : ℂ)‖ < 1 := by
    simpa using hz
  have hre : 0 < (1 + c / z ^ (2 ^ N)).re :=
    re_pos_of_norm_sub_one_lt_one hlt'
  exact abs_arg_lt_pi_div_two_of_re_pos hre

lemma eventually_atInfinity_abs_arg_lt_pi_div_two_quadratic_iter_ratio_sq
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity,
      |Complex.arg (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)| < Real.pi / 2 := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have harg : Tendsto (fun z => Complex.arg (g z)) atInfinity (𝓝 (0 : ℝ)) := by
    have harg' : Tendsto (fun z => Complex.arg (g z)) atInfinity (𝓝 (Complex.arg (1 : ℂ))) := by
      have hcont : ContinuousAt Complex.arg (1 : ℂ) := by
        exact
          (Complex.continuousAt_arg (by exact (one_mem_slitPlane : (1 : ℂ) ∈ Complex.slitPlane)))
      exact hcont.tendsto.comp hG
    simpa using harg'
  have hball : Metric.ball (0 : ℝ) (Real.pi / 4) ∈ 𝓝 (0 : ℝ) := by
    have hpi : (0 : ℝ) < Real.pi / 4 := by nlinarith [Real.pi_pos]
    exact Metric.ball_mem_nhds _ hpi
  have hargsmall : ∀ᶠ z in atInfinity, |Complex.arg (g z)| < Real.pi / 4 := by
    have h := tendsto_def.1 harg _ hball
    simpa [Metric.ball, Set.mem_setOf_eq, Real.dist_eq] using h
  have hne : ∀ᶠ z in atInfinity, g z ≠ 0 :=
    hG.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have hboth : ∀ᶠ z in atInfinity, g z ≠ 0 ∧ |Complex.arg (g z)| < Real.pi / 4 :=
    hne.and hargsmall
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hzne, hzarg⟩
  have hzarg' : |Complex.arg (g z)| < Real.pi / 2 := by
    nlinarith [hzarg, Real.pi_pos]
  have hsum : Complex.arg (g z) + Complex.arg (g z) ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_abs_lt_pi_div_two hzarg' hzarg'
  have hargmul : Complex.arg (g z * g z) = Complex.arg (g z) + Complex.arg (g z) :=
    (Complex.arg_mul_eq_add_arg_iff hzne hzne).2 hsum
  have hargpow : Complex.arg ((g z) ^ 2) = Complex.arg (g z) + Complex.arg (g z) := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hargmul
  have hlt' : |Complex.arg (g z) + Complex.arg (g z)| < Real.pi / 2 := by
    calc
      |Complex.arg (g z) + Complex.arg (g z)|
          = |(2 : ℝ) * Complex.arg (g z)| := by ring_nf
      _ = (2 : ℝ) * |Complex.arg (g z)| := by simp
      _ < (2 : ℝ) * (Real.pi / 4) := by nlinarith [hzarg]
      _ = Real.pi / 2 := by ring_nf
  have hlt : |Complex.arg ((g z) ^ 2)| < Real.pi / 2 := by
    rw [hargpow]
    exact hlt'
  exact hlt

lemma eventually_atInfinity_abs_arg_lt_pi_div_two_ratio_term
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity,
      |Complex.arg
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)|
        < Real.pi / 2 := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
    have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
    simpa using (hcont.tendsto (1 : ℂ)).comp hG
  have hG2inv : Tendsto (fun z => ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
    have h := (continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto.comp hG2
    simpa using h
  have ht : Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
    have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
    exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
  have hprod :
      Tendsto (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹) atInfinity (𝓝 (0 : ℂ)) := by
    simpa using ht.mul hG2inv
  have hsum :
      Tendsto (fun z : ℂ => (1 : ℂ) +
        (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.add hprod)
  have hball : Metric.ball (1 : ℂ) 1 ∈ 𝓝 (1 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
  have hlt : ∀ᶠ z in atInfinity,
      ‖(1 : ℂ) + (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹ - (1 : ℂ)‖ < 1 := by
    have h := tendsto_def.1 hsum _ hball
    simpa [Metric.ball, Set.mem_setOf_eq, dist_eq_norm] using h
  refine hlt.mono ?_
  intro z hz
  have hlt' :
      ‖(1 : ℂ) + (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹ - (1 : ℂ)‖ < 1 := hz
  have hre :
      0 < ((1 : ℂ) + (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹).re :=
    re_pos_of_norm_sub_one_lt_one hlt'
  have harg : |Complex.arg ((1 : ℂ) + (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹)|
      < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos hre
  simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using harg

lemma eventually_atInfinity_abs_arg_lt_quadratic_iter_ratio_sq_of_pos
    (c : ℂ) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in atInfinity,
      |Complex.arg (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)| < ε := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
    have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
    simpa using (hcont.tendsto (1 : ℂ)).comp hG
  have harg : Tendsto (fun z => Complex.arg ((g z) ^ 2)) atInfinity (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousAt Complex.arg (1 : ℂ) := by
      exact (Complex.continuousAt_arg (by exact (one_mem_slitPlane : (1 : ℂ) ∈ Complex.slitPlane)))
    have h := hcont.tendsto.comp hG2
    simpa using h
  have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have h := tendsto_def.1 harg _ hball
  simpa [Metric.ball, Set.mem_setOf_eq, Real.dist_eq] using h

lemma eventually_atInfinity_abs_arg_lt_ratio_term_of_pos
    (c : ℂ) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in atInfinity,
      |Complex.arg
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)|
        < ε := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
    have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
    simpa using (hcont.tendsto (1 : ℂ)).comp hG
  have hG2inv : Tendsto (fun z => ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
    have h := (continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto.comp hG2
    simpa using h
  have ht : Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
    have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
    exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
  have hprod :
      Tendsto (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹) atInfinity (𝓝 (0 : ℂ)) := by
    simpa using ht.mul hG2inv
  have hsum :
      Tendsto (fun z : ℂ =>
          (1 : ℂ) + (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
    simpa using (tendsto_const_nhds.add hprod)
  have harg : Tendsto
      (fun z =>
        Complex.arg ((1 : ℂ) + (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹))
      atInfinity (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousAt Complex.arg (1 : ℂ) := by
      exact (Complex.continuousAt_arg (by exact (one_mem_slitPlane : (1 : ℂ) ∈ Complex.slitPlane)))
    have h := hcont.tendsto.comp hsum
    simpa using h
  have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have h := tendsto_def.1 harg _ hball
  simpa [Metric.ball, Set.mem_setOf_eq, Real.dist_eq, g, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using h

lemma eventually_atInfinity_abs_arg_lt_pi_div_four_candidate
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity,
      |Complex.arg
          (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))|
        < Real.pi / 2 := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hε : 0 < (Real.pi / 4) := by
    nlinarith [Real.pi_pos]
  have harg1 : ∀ᶠ z in atInfinity, |Complex.arg ((g z) ^ 2)| < Real.pi / 4 :=
    eventually_atInfinity_abs_arg_lt_quadratic_iter_ratio_sq_of_pos c N (Real.pi / 4) hε
  have harg2 : ∀ᶠ z in atInfinity,
      |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 4 :=
    eventually_atInfinity_abs_arg_lt_ratio_term_of_pos c N (Real.pi / 4) hε
  have hne : ∀ᶠ z in atInfinity, g z ≠ 0 := by
    have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
      tendsto_quadratic_iter_div_pow_atInfinity c N
    exact hG.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have hterm_ne : ∀ᶠ z in atInfinity,
      (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ≠ 0 := by
    have hterm : Tendsto (fun z => (1 : ℂ) + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)
        atInfinity (𝓝 (1 : ℂ)) := by
      have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
        have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
        simpa using (hcont.tendsto (1 : ℂ)).comp
          (tendsto_quadratic_iter_div_pow_atInfinity c N)
      have hG2inv : Tendsto (fun z => ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
        have h := (continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto.comp hG2
        simpa using h
      have ht : Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
        have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
        exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
      have hprod :
          Tendsto (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹)
            atInfinity (𝓝 (0 : ℂ)) := by
        simpa using ht.mul hG2inv
      simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (tendsto_const_nhds.add hprod)
    exact hterm.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have hboth : ∀ᶠ z in atInfinity,
      g z ≠ 0 ∧
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ≠ 0 ∧
          |Complex.arg ((g z) ^ 2)| < Real.pi / 4 ∧
            |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 4 :=
    hne.and (hterm_ne.and (harg1.and harg2))
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hgne, htermne, harg1z, harg2z⟩
  have hsum : Complex.arg ((g z) ^ 2) + Complex.arg
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_abs_lt_pi_div_two
      (by nlinarith [harg1z, Real.pi_pos])
      (by nlinarith [harg2z, Real.pi_pos])
  have hargmul :
      Complex.arg ((g z) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)) =
        Complex.arg ((g z) ^ 2) +
          Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) :=
    (Complex.arg_mul_eq_add_arg_iff (by exact pow_ne_zero 2 hgne) htermne).2 hsum
  have hlt : |Complex.arg ((g z) ^ 2) + Complex.arg
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 2 := by
    have h1 : |Complex.arg ((g z) ^ 2)| < Real.pi / 4 := harg1z
    have h2 : |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 4 := harg2z
    have htri :
        |Complex.arg ((g z) ^ 2) + Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| ≤
          |Complex.arg ((g z) ^ 2)| +
            |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| := by
      simpa using
        (norm_add_le (Complex.arg ((g z) ^ 2))
          (Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)))
    nlinarith [h1, h2, htri]
  have hlt' :
      |Complex.arg ((g z) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2))| < Real.pi / 2 := by
    simpa [hargmul] using hlt
  simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlt'

lemma abs_arg_pow_lt_pi_div_two_of_abs_arg_lt
    {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (harg : |Complex.arg z| < Real.pi / (2 * (n : ℝ))) :
    |Complex.arg (z ^ n)| < Real.pi / 2 := by
  have hn' : (0 : ℝ) < n := by
    exact_mod_cast (Nat.pos_of_ne_zero hn)
  -- `arg(z^n)` is the `n`-multiple of `arg z` in `Real.Angle`.
  have hcoe : (Complex.arg (z ^ n) : Real.Angle) = n • (Complex.arg z : Real.Angle) := by
    simpa using (Complex.arg_pow_coe_angle z n)
  have htoReal :
      (Complex.arg (z ^ n) : Real.Angle).toReal =
        (n • (Complex.arg z : Real.Angle)).toReal := by
    simp [hcoe]
  have hleft :
      |Complex.arg (z ^ n)| =
        |(n • (Complex.arg z : Real.Angle)).toReal| := by
    calc
      |Complex.arg (z ^ n)| = |(Complex.arg (z ^ n) : Real.Angle).toReal| := by
        simp [Complex.arg_coe_angle_toReal_eq_arg]
      _ = |(n • (Complex.arg z : Real.Angle)).toReal| := by
        simp [htoReal]
  -- From `|arg z| < π/(2n)` we get `arg z ∈ Ioc (-π/n, π/n)`.
  have harg' : |Complex.arg z| < Real.pi / (n : ℝ) := by
    have hle : Real.pi / (2 * (n : ℝ)) ≤ Real.pi / (n : ℝ) := by
      have hcmp : (n : ℝ) ≤ 2 * (n : ℝ) := by nlinarith [hn']
      have h1 : (1 : ℝ) / (2 * (n : ℝ)) ≤ 1 / (n : ℝ) := by
        exact one_div_le_one_div_of_le hn' hcmp
      have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
      calc
        Real.pi / (2 * (n : ℝ)) = Real.pi * (1 / (2 * (n : ℝ))) := by ring
        _ ≤ Real.pi * (1 / (n : ℝ)) := by
              exact mul_le_mul_of_nonneg_left h1 hpi
        _ = Real.pi / (n : ℝ) := by ring
    exact lt_of_lt_of_le harg hle
  have hmem' : Complex.arg z ∈ Set.Ioc (-Real.pi / (n : ℝ)) (Real.pi / (n : ℝ)) := by
    refine ⟨?_, ?_⟩
    ·
      have h := (abs_lt.1 harg').1
      simpa [neg_div] using h
    · exact le_of_lt (abs_lt.1 harg').2
  have hmem : (Complex.arg z : Real.Angle).toReal ∈
      Set.Ioc (-Real.pi / (n : ℝ)) (Real.pi / (n : ℝ)) := by
    simpa [Complex.arg_coe_angle_toReal_eq_arg] using hmem'
  have hmul :
      (n • (Complex.arg z : Real.Angle)).toReal =
        (n : ℝ) * (Complex.arg z : Real.Angle).toReal :=
    (Real.Angle.nsmul_toReal_eq_mul hn).2 hmem
  have hmul' :
      |(n • (Complex.arg z : Real.Angle)).toReal|
        = (n : ℝ) * |(Complex.arg z : Real.Angle).toReal| := by
    have hn0 : 0 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.cast_nonneg n)
    calc
      |(n • (Complex.arg z : Real.Angle)).toReal|
          = |(n : ℝ) * (Complex.arg z : Real.Angle).toReal| := by
              simp [hmul]
      _ = (n : ℝ) * |(Complex.arg z : Real.Angle).toReal| := by
              simp [abs_mul, abs_of_nonneg hn0]
  have hmul'' : (n : ℝ) * |(Complex.arg z : Real.Angle).toReal| < Real.pi / 2 := by
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_ne_zero hn))
    have hmul : (n : ℝ) * |Complex.arg z| < (n : ℝ) * (Real.pi / (2 * (n : ℝ))) := by
      exact (mul_lt_mul_of_pos_left harg hn')
    have hmul' : (n : ℝ) * (Real.pi / (2 * (n : ℝ))) = Real.pi / 2 := by
      field_simp [hn0]
    have : (n : ℝ) * |Complex.arg z| < Real.pi / 2 := by
      simpa [hmul'] using hmul
    simpa [Complex.arg_coe_angle_toReal_eq_arg] using this
  have hbound :
      |(n • (Complex.arg z : Real.Angle)).toReal| < Real.pi / 2 := by
    simpa [hmul'] using hmul''
  simpa [hleft] using hbound

lemma eventually_atInfinity_cpow_mul_split
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity,
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
          ((2 : ℂ) ^ (N + 1))⁻¹
        =
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2) ^ ((2 : ℂ) ^ (N + 1))⁻¹ *
        (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2) ^
          ((2 : ℂ) ^ (N + 1))⁻¹ := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hne : ∀ᶠ z in atInfinity, g z ≠ 0 :=
    hG.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have harg1 : ∀ᶠ z in atInfinity, |Complex.arg ((g z) ^ 2)| < Real.pi / 2 :=
    eventually_atInfinity_abs_arg_lt_pi_div_two_quadratic_iter_ratio_sq c N
  have harg2 : ∀ᶠ z in atInfinity,
      |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 2 :=
    eventually_atInfinity_abs_arg_lt_pi_div_two_ratio_term c N
  have hterm_ne : ∀ᶠ z in atInfinity,
      (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ≠ 0 := by
    have hterm : Tendsto (fun z => (1 : ℂ) + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)
        atInfinity (𝓝 (1 : ℂ)) := by
      -- reuse the construction from the ratio-term lemma
      have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
        have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
        simpa using (hcont.tendsto (1 : ℂ)).comp hG
      have hG2inv : Tendsto (fun z => ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
        have h := (continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto.comp hG2
        simpa using h
      have ht : Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
        have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
        exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
      have hprod :
          Tendsto (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹) atInfinity (𝓝 (0 : ℂ)) := by
        simpa using ht.mul hG2inv
      simpa using (tendsto_const_nhds.add hprod)
    exact hterm.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have hboth : ∀ᶠ z in atInfinity,
      g z ≠ 0 ∧
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ≠ 0 ∧
          |Complex.arg ((g z) ^ 2)| < Real.pi / 2 ∧
            |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 2 :=
    hne.and (hterm_ne.and (harg1.and harg2))
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hgne, htermne, harg1z, harg2z⟩
  have hsum : Complex.arg ((g z) ^ 2) + Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ∈
      Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_abs_lt_pi_div_two harg1z harg2z
  have hmul :
      Complex.log (((g z) ^ 2) * (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)) =
        Complex.log ((g z) ^ 2) + Complex.log (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) :=
    (Complex.log_mul_eq_add_log_iff (by exact pow_ne_zero 2 hgne) htermne).2 hsum
  have hpow := cpow_mul_of_log_mul ((g z) ^ 2)
    (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ((2 : ℂ) ^ (N + 1))⁻¹
    (by exact pow_ne_zero 2 hgne) htermne hmul
  simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpow

lemma tendsto_quadratic_iter_ratio_sq_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto (fun z => ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
      atInfinity (𝓝 (1 : ℂ)) := by
  have hG : Tendsto (fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)) atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
  simpa using (hcont.tendsto (1 : ℂ)).comp hG

lemma tendsto_ratio_term_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto
      (fun z =>
        (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
      atInfinity (𝓝 (0 : ℂ)) := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
    have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
    simpa using (hcont.tendsto (1 : ℂ)).comp hG
  have hG2inv : Tendsto (fun z => ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
    have h := (continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto.comp hG2
    simpa using h
  have ht : Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
    have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
    exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
  have hprod :
      Tendsto (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹)
        atInfinity (𝓝 (0 : ℂ)) := by
    simpa using ht.mul hG2inv
  simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hprod

lemma tendsto_root_ratio_term_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto
      (fun z =>
        (1 : ℂ) +
          (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
      atInfinity (𝓝 (1 : ℂ)) := by
  have hterm : Tendsto
      (fun z =>
        (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
      atInfinity (𝓝 (0 : ℂ)) :=
    tendsto_ratio_term_atInfinity c N
  simpa using (tendsto_const_nhds.add hterm)

lemma tendsto_root_seq_ratio_candidate_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto
      (fun z =>
        (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
            ((2 : ℂ) ^ (N + 1))⁻¹)
      atInfinity (𝓝 (1 : ℂ)) := by
  have hG2 : Tendsto
      (fun z => ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
      atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_ratio_sq_atInfinity c N
  have hterm :
      Tendsto
        (fun z =>
          (1 : ℂ) +
            (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
        atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_root_ratio_term_atInfinity c N
  have hprod :
      Tendsto
        (fun z =>
          ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) /
              ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
        atInfinity (𝓝 (1 : ℂ)) := by
    simpa using hG2.mul hterm
  exact tendsto_cpow_const_of_tendsto_one (f := fun z =>
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) /
          ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)))
    (a := ((2 : ℂ) ^ (N + 1))⁻¹) hprod

lemma root_seq_ratio_candidate_eq_div
    (c : ℂ) (N : ℕ) (z : ℂ) (hz : z ≠ 0)
    (hA : (quadratic_map c)^[N] z ≠ 0) :
    (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
      = (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) := by
  have hz' : z ^ (2 ^ (N + 1)) ≠ 0 := by
    exact pow_ne_zero _ hz
  have hA' : ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ≠ 0 := by
    have hB : z ^ (2 ^ N) ≠ 0 := by
      exact pow_ne_zero _ hz
    exact div_ne_zero hA hB
  have hpow : z ^ (2 ^ (N + 1)) = (z ^ (2 ^ N)) ^ 2 := by
    simp [pow_mul, pow_succ]
  field_simp [hz', hA', hpow, pow_succ, pow_mul, mul_comm, mul_left_comm, mul_assoc]
  ring

lemma pow_cpow_nat_inv_of_abs_arg_lt {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (harg : |Complex.arg z| < Real.pi / n) :
    (z ^ n) ^ ((n⁻¹ : ℂ)) = z := by
  have hlt : -(Real.pi / n) < Complex.arg z := by
    have h := (abs_lt.1 harg).1
    linarith
  have hle : Complex.arg z ≤ Real.pi / n := by
    have h := (abs_lt.1 harg).2
    linarith
  exact Complex.pow_cpow_nat_inv hn hlt hle

lemma correction_factor_eq_one_of_abs_arg_lt {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ≠ 0)
    (harg : |Complex.arg z| < Real.pi / n) :
    (z ^ n) ^ ((n⁻¹ : ℂ)) / z = (1 : ℂ) := by
  have h := pow_cpow_nat_inv_of_abs_arg_lt (z := z) (n := n) hn harg
  simp [h, hz]

lemma log_mul_eq_add_log_of_abs_arg_lt_pi_div_two
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxarg : |Complex.arg x| < Real.pi / 2)
    (hyarg : |Complex.arg y| < Real.pi / 2) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hsum : Complex.arg x + Complex.arg y ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_abs_lt_pi_div_two hxarg hyarg
  exact (Complex.log_mul_eq_add_log_iff hx hy).2 hsum

lemma log_mul_eq_add_log_candidate_of_sector
    (c : ℂ) (N : ℕ) (z : ℂ)
    (hz : z ≠ 0)
    (hA0 : (quadratic_map c)^[N] z ≠ 0)
    (hA : ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0)
    (hcand_arg :
      |Complex.arg
          (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))|
        < Real.pi / 2)
    (hzarg : |Complex.arg z| < Real.pi / (2 * (2 ^ (N + 1) : ℝ))) :
    Complex.log (((quadratic_map c)^[N] z) ^ 2 + c) =
      Complex.log
          (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) +
        Complex.log (z ^ (2 ^ (N + 1))) := by
  let cand : ℂ :=
    ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
      (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
  have hrewrite : cand = (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) := by
    simpa [cand] using (root_seq_ratio_candidate_eq_div c N z hz hA0)
  have hzy : z ^ (2 ^ (N + 1)) ≠ 0 := by
    exact pow_ne_zero _ hz
  have hcand_ne : cand ≠ 0 := by
    have : (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) ≠ 0 := by
      exact div_ne_zero hA hzy
    simpa [hrewrite] using this
  have hyarg : |Complex.arg (z ^ (2 ^ (N + 1)))| < Real.pi / 2 := by
    have hn : (2 ^ (N + 1) : ℕ) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)
    have hzarg' : |Complex.arg z| < Real.pi / (2 * ((2 ^ (N + 1) : ℕ) : ℝ)) := by
      simpa using hzarg
    exact abs_arg_pow_lt_pi_div_two_of_abs_arg_lt (n := 2 ^ (N + 1)) hn hzarg'
  have hlog :=
    log_mul_eq_add_log_of_abs_arg_lt_pi_div_two
      (x := cand) (y := z ^ (2 ^ (N + 1))) hcand_ne hzy hcand_arg hyarg
  -- `cand * z^(2^(N+1)) = A`.
  have hmul : cand * z ^ (2 ^ (N + 1)) = ((quadratic_map c)^[N] z) ^ 2 + c := by
    calc
      cand * z ^ (2 ^ (N + 1))
          = (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) *
              z ^ (2 ^ (N + 1)) := by
                simp [hrewrite]
      _ = ((quadratic_map c)^[N] z) ^ 2 + c := by
            field_simp [hzy]
  simpa [hmul, cand] using hlog


lemma eventually_atInfinity_log_candidate_eq_add
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity,
      Complex.log
          (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
        =
      Complex.log (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2) +
        Complex.log
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2) := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hne : ∀ᶠ z in atInfinity, g z ≠ 0 :=
    hG.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have harg1 : ∀ᶠ z in atInfinity, |Complex.arg ((g z) ^ 2)| < Real.pi / 2 :=
    eventually_atInfinity_abs_arg_lt_pi_div_two_quadratic_iter_ratio_sq c N
  have harg2 : ∀ᶠ z in atInfinity,
      |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 2 :=
    eventually_atInfinity_abs_arg_lt_pi_div_two_ratio_term c N
  have hterm_ne : ∀ᶠ z in atInfinity,
      (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ≠ 0 := by
    have hterm : Tendsto (fun z => (1 : ℂ) + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)
        atInfinity (𝓝 (1 : ℂ)) := by
      have hG2 : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
        have hcont : Continuous (fun w : ℂ => w ^ 2) := (continuous_id.pow 2)
        simpa using (hcont.tendsto (1 : ℂ)).comp hG
      have hG2inv : Tendsto (fun z => ((g z) ^ 2)⁻¹) atInfinity (𝓝 (1 : ℂ)) := by
        have h := (continuousAt_inv₀ (by norm_num : (1 : ℂ) ≠ 0)).tendsto.comp hG2
        simpa using h
      have ht : Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) := by
        have hk : 0 < 2 ^ (N + 1) := pow_pos (by norm_num : (0 : ℕ) < 2) _
        exact tendsto_atInfinity_const_div_pow_zero c (2 ^ (N + 1)) hk
      have hprod :
          Tendsto (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) * ((g z) ^ 2)⁻¹)
            atInfinity (𝓝 (0 : ℂ)) := by
        simpa using ht.mul hG2inv
      simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (tendsto_const_nhds.add hprod)
    exact hterm.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have hboth : ∀ᶠ z in atInfinity,
      g z ≠ 0 ∧
        (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2) ≠ 0 ∧
          |Complex.arg ((g z) ^ 2)| < Real.pi / 2 ∧
            |Complex.arg (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2)| < Real.pi / 2 :=
    hne.and (hterm_ne.and (harg1.and harg2))
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hgne, htermne, harg1z, harg2z⟩
  have hlog := log_mul_eq_add_log_of_abs_arg_lt_pi_div_two
    (x := (g z) ^ 2)
    (y := (1 + (c / z ^ (2 ^ (N + 1))) / (g z) ^ 2))
    (hx := by exact pow_ne_zero 2 hgne)
    (hy := htermne)
    (hxarg := harg1z)
    (hyarg := harg2z)
  simpa [g, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog

lemma bottcher_root_seq_ratio_eq_candidate_of_log_and_arg
    (c : ℂ) (N : ℕ) (z : ℂ) (hz : z ≠ 0)
    (hA0 : (quadratic_map c)^[N] z ≠ 0)
    (hA : ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0)
    (hlog :
      Complex.log (((quadratic_map c)^[N] z) ^ 2 + c) =
        Complex.log ((((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1))) +
          Complex.log (z ^ (2 ^ (N + 1))))
    (harg : |Complex.arg z| < Real.pi / (2 ^ (N + 1))) :
    bottcher_root_seq c (N + 1) z / z =
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
        ((2 : ℂ) ^ (N + 1))⁻¹ := by
  let A : ℂ := ((quadratic_map c)^[N] z) ^ 2 + c
  let x : ℂ := A / z ^ (2 ^ (N + 1))
  let y : ℂ := z ^ (2 ^ (N + 1))
  have hz' : y ≠ 0 := by
    dsimp [y]
    exact pow_ne_zero _ hz
  have hx : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero hA hz'
  have hxy : x * y = A := by
    dsimp [x, y]
    field_simp [hz']
  have hlog' : Complex.log (x * y) = Complex.log x + Complex.log y := by
    simpa [x, y, hxy] using hlog
  have hsplit :
      (x * y) ^ ((2 : ℂ) ^ (N + 1))⁻¹ =
        x ^ ((2 : ℂ) ^ (N + 1))⁻¹ * y ^ ((2 : ℂ) ^ (N + 1))⁻¹ :=
    cpow_mul_of_log_mul x y ((2 : ℂ) ^ (N + 1))⁻¹ hx hz' hlog'
  have hrewrite :
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
        = x := by
    have h := root_seq_ratio_candidate_eq_div c N z hz hA0
    simpa [x] using h
  have hcorr :
      y ^ ((2 : ℂ) ^ (N + 1))⁻¹ / z = (1 : ℂ) := by
    have hn : (2 ^ (N + 1) : ℕ) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)
    have harg' : |Complex.arg z| < Real.pi / (2 ^ (N + 1) : ℕ) := by
      simpa using harg
    simpa [y] using
      (correction_factor_eq_one_of_abs_arg_lt (z := z) (n := 2 ^ (N + 1)) hn hz harg')
  calc
    bottcher_root_seq c (N + 1) z / z
        = (((fun w => w ^ 2 + c)^[N] z) ^ 2 + c) ^ ((2 : ℂ) ^ (N + 1))⁻¹ / z := by
            simp [bottcher_root_seq_succ]
    _ = A ^ ((2 : ℂ) ^ (N + 1))⁻¹ / z := by
            change (((quadratic_map c)^[N] z) ^ 2 + c) ^ ((2 : ℂ) ^ (N + 1))⁻¹ / z =
              A ^ ((2 : ℂ) ^ (N + 1))⁻¹ / z
            simp [A]
    _ = (x ^ ((2 : ℂ) ^ (N + 1))⁻¹ * y ^ ((2 : ℂ) ^ (N + 1))⁻¹) / z := by
            -- replace `A` by `x*y` and use the log-branch split
            simpa [A, hxy] using congrArg (fun t => t / z) hsplit
    _ = x ^ ((2 : ℂ) ^ (N + 1))⁻¹ := by
            -- use the correction factor
            calc
              (x ^ ((2 : ℂ) ^ (N + 1))⁻¹ * y ^ ((2 : ℂ) ^ (N + 1))⁻¹) / z
                  = x ^ ((2 : ℂ) ^ (N + 1))⁻¹ * (y ^ ((2 : ℂ) ^ (N + 1))⁻¹ / z) := by
                      ring
              _ = x ^ ((2 : ℂ) ^ (N + 1))⁻¹ := by
                      simp [hcorr]
    _ =
        (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
          ((2 : ℂ) ^ (N + 1))⁻¹ := by
            simp [hrewrite]

lemma bottcher_root_seq_ratio_eq_candidate_of_sector
    (c : ℂ) (N : ℕ) (z : ℂ)
    (hz : z ≠ 0)
    (hA0 : (quadratic_map c)^[N] z ≠ 0)
    (hA : ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0)
    (hcand_arg :
      |Complex.arg
          (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))|
        < Real.pi / 2)
    (hzarg : |Complex.arg z| < Real.pi / (2 * (2 ^ (N + 1) : ℝ))) :
    bottcher_root_seq c (N + 1) z / z =
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
        ((2 : ℂ) ^ (N + 1))⁻¹ := by
  have hlog := log_mul_eq_add_log_candidate_of_sector c N z hz hA0 hA hcand_arg hzarg
  have hlog' :
      Complex.log (((quadratic_map c)^[N] z) ^ 2 + c) =
        Complex.log ((((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1))) +
          Complex.log (z ^ (2 ^ (N + 1))) := by
    -- rewrite the candidate as `A / z^(2^(N+1))`
    have hrewrite :
        (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
          = (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) := by
      simpa using (root_seq_ratio_candidate_eq_div c N z hz hA0)
    simpa [hrewrite] using hlog
  have hzarg' :
      |Complex.arg z| < Real.pi / (2 ^ (N + 1) : ℝ) := by
    have hpos : (0 : ℝ) < (2 ^ (N + 1) : ℝ) := by
      exact pow_pos (by norm_num : (0 : ℝ) < 2) _
    have hle' : (2 ^ (N + 1) : ℝ) ≤ 2 * (2 ^ (N + 1) : ℝ) := by
      nlinarith
    have hle'' :
        (1 : ℝ) / (2 * (2 ^ (N + 1) : ℝ)) ≤ (1 : ℝ) / (2 ^ (N + 1) : ℝ) :=
      one_div_le_one_div_of_le hpos hle'
    have hpi : 0 ≤ (Real.pi : ℝ) := le_of_lt Real.pi_pos
    have hle :
        Real.pi / (2 * (2 ^ (N + 1) : ℝ)) ≤ Real.pi / (2 ^ (N + 1) : ℝ) := by
      simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hle'' hpi)
    exact lt_of_lt_of_le hzarg hle
  exact bottcher_root_seq_ratio_eq_candidate_of_log_and_arg
    c N z hz hA0 hA hlog' hzarg'
lemma eventually_atInfinity_iter_ne_zero (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity, (quadratic_map c)^[N] z ≠ 0 := by
  let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
  have hG : Tendsto g atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_quadratic_iter_div_pow_atInfinity c N
  have hne : ∀ᶠ z in atInfinity, g z ≠ 0 :=
    hG.eventually_ne (by exact (one_ne_zero : (1 : ℂ) ≠ (0 : ℂ)))
  have hzne : ∀ᶠ z in atInfinity, z ≠ 0 := by
    have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
      eventually_atInfinity_norm_gt (0 : ℝ)
    exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
  have hboth : ∀ᶠ z in atInfinity, g z ≠ 0 ∧ z ≠ 0 := hne.and hzne
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hgz, hz⟩
  have hzn : z ^ (2 ^ N) ≠ 0 := pow_ne_zero _ hz
  exact (div_ne_zero_iff.mp hgz).1

lemma eventually_atInfinity_root_seq_ratio_candidate_eq_div
    (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity,
      (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
          (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) =
        (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) := by
  have hA : ∀ᶠ z in atInfinity, (quadratic_map c)^[N] z ≠ 0 :=
    eventually_atInfinity_iter_ne_zero c N
  have hzne : ∀ᶠ z in atInfinity, z ≠ 0 := by
    have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
      eventually_atInfinity_norm_gt (0 : ℝ)
    exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
  have hboth : ∀ᶠ z in atInfinity, z ≠ 0 ∧ (quadratic_map c)^[N] z ≠ 0 :=
    hzne.and hA
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hz, hA⟩
  exact root_seq_ratio_candidate_eq_div c N z hz hA

def arg_sector (N : ℕ) : Set ℂ :=
  {z | |Complex.arg z| < Real.pi / (2 * (2 ^ (N + 1) : ℝ))}

lemma eventually_atInfinity_iter_sq_add_c_ne_zero (c : ℂ) (N : ℕ) :
    ∀ᶠ z in atInfinity, ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0 := by
  let cand : ℂ → ℂ := fun z =>
    (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
      ((2 : ℂ) ^ (N + 1))⁻¹
  have hCand : Tendsto cand atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_root_seq_ratio_candidate_atInfinity c N
  have hCand_ne : ∀ᶠ z in atInfinity, cand z ≠ 0 :=
    hCand.eventually_ne (by exact one_ne_zero)
  have hdiv :
      ∀ᶠ z in atInfinity,
        (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) =
          (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) :=
    eventually_atInfinity_root_seq_ratio_candidate_eq_div c N
  have hzne : ∀ᶠ z in atInfinity, z ≠ 0 := by
    have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
      eventually_atInfinity_norm_gt (0 : ℝ)
    exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
  have hboth := hCand_ne.and (hdiv.and hzne)
  refine hboth.mono ?_
  intro z hz
  rcases hz with ⟨hcand, hdiv, hzne⟩
  have hzpow : z ^ (2 ^ (N + 1)) ≠ 0 := pow_ne_zero _ hzne
  intro hA
  have hdiv' :
      cand z =
        ((((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1))) ^
          ((2 : ℂ) ^ (N + 1))⁻¹ := by
    simp [cand, hdiv]
  have : cand z = 0 := by
    have hzero : (((quadratic_map c)^[N] z) ^ 2 + c) / z ^ (2 ^ (N + 1)) = 0 := by
      simp [hA]
    simp [hdiv', hzero]
  exact hcand this

lemma tendsto_bottcher_root_seq_ratio_atInfinity_in_sector
    (c : ℂ) (N : ℕ) :
    Tendsto (fun z => bottcher_root_seq c (N + 1) z / z)
      (atInfinity ⊓ 𝓟 (arg_sector N)) (𝓝 (1 : ℂ)) := by
  let cand : ℂ → ℂ := fun z =>
    (( (quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
        (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)) ^
      ((2 : ℂ) ^ (N + 1))⁻¹
  have hCand : Tendsto cand atInfinity (𝓝 (1 : ℂ)) :=
    tendsto_root_seq_ratio_candidate_atInfinity c N
  have hCand' : Tendsto cand (atInfinity ⊓ 𝓟 (arg_sector N)) (𝓝 (1 : ℂ)) :=
    hCand.mono_left inf_le_left
  have hA0 : ∀ᶠ z in atInfinity, (quadratic_map c)^[N] z ≠ 0 :=
    eventually_atInfinity_iter_ne_zero c N
  have hA : ∀ᶠ z in atInfinity, ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0 :=
    eventually_atInfinity_iter_sq_add_c_ne_zero c N
  have hargCand : ∀ᶠ z in atInfinity,
      |Complex.arg
          (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
            (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))|
        < Real.pi / 2 :=
    eventually_atInfinity_abs_arg_lt_pi_div_four_candidate c N
  have hzne : ∀ᶠ z in atInfinity, z ≠ 0 := by
    have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
      eventually_atInfinity_norm_gt (0 : ℝ)
    exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
  have hsector :
      ∀ᶠ z in (atInfinity ⊓ 𝓟 (arg_sector N)),
        |Complex.arg z| < Real.pi / (2 * (2 ^ (N + 1) : ℝ)) := by
    have : ∀ᶠ z in (𝓟 (arg_sector N)),
        |Complex.arg z| < Real.pi / (2 * (2 ^ (N + 1) : ℝ)) := by
      exact Filter.eventually_principal.2 (by intro z hz; exact hz)
    exact this.filter_mono inf_le_right
  have hbase :
      ∀ᶠ z in atInfinity,
        z ≠ 0 ∧
          (quadratic_map c)^[N] z ≠ 0 ∧
            ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0 ∧
              |Complex.arg
                  (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
                    (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))|
                < Real.pi / 2 := by
    exact hzne.and (hA0.and (hA.and hargCand))
  have hbase' :
      ∀ᶠ z in (atInfinity ⊓ 𝓟 (arg_sector N)),
        z ≠ 0 ∧
          (quadratic_map c)^[N] z ≠ 0 ∧
            ((quadratic_map c)^[N] z) ^ 2 + c ≠ 0 ∧
              |Complex.arg
                  (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 *
                    (1 + (c / z ^ (2 ^ (N + 1))) / ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))|
                < Real.pi / 2 := by
    exact hbase.filter_mono inf_le_left
  have hEq :
      ∀ᶠ z in (atInfinity ⊓ 𝓟 (arg_sector N)),
        bottcher_root_seq c (N + 1) z / z = cand z := by
    refine (hbase'.and hsector).mono ?_
    intro z hz
    rcases hz with ⟨⟨hzne, hA0, hA, hargCand⟩, hzarg⟩
    have hzarg' :
        |Complex.arg z| < Real.pi / (2 * (2 ^ (N + 1) : ℝ)) := hzarg
    have h := bottcher_root_seq_ratio_eq_candidate_of_sector
      (c := c) (N := N) (z := z) hzne hA0 hA hargCand hzarg'
    simpa [cand] using h
  exact (tendsto_congr' hEq).2 hCand'


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

lemma potential_seq_eq_log_norm_iterate
    (c : ℂ) (z : ℂ) (n : ℕ)
    (h1 : 1 ≤ ‖(quadratic_map c)^[n] z‖) :
    Quadratic.potential_seq c z n =
      (1 / 2 ^ n) * Real.log ‖(quadratic_map c)^[n] z‖ := by
  dsimp [Quadratic.potential_seq]
  have hmax : max 1 ‖Quadratic.orbit c z n‖ = ‖Quadratic.orbit c z n‖ := by
    exact max_eq_right h1
  have horb : Quadratic.orbit c z n = (quadratic_map c)^[n] z := by
    rfl
  have hmax' : max 1 ‖(quadratic_map c)^[n] z‖ = ‖(quadratic_map c)^[n] z‖ := by
    exact max_eq_right h1
  simp [horb, hmax']

lemma bottcher_root_seq_norm_eq_exp_potential
    (c : ℂ) (z : ℂ) (n : ℕ)
    (h1 : 1 ≤ ‖(quadratic_map c)^[n] z‖) :
    ‖bottcher_root_seq c n z‖ = Real.exp (Quadratic.potential_seq c z n) := by
  have hzero : (quadratic_map c)^[n] z ≠ 0 := by
    have hpos : 0 < ‖(quadratic_map c)^[n] z‖ := lt_of_lt_of_le zero_lt_one h1
    exact (norm_ne_zero_iff).1 (ne_of_gt hpos)
  have hnorm :
      ‖bottcher_root_seq c n z‖ =
        ‖(quadratic_map c)^[n] z‖ ^ ((1 : ℝ) / (2 : ℝ) ^ n) :=
    norm_bottcher_root_seq_eq_rpow_of_ne_zero (c := c) (n := n) (z := z) hzero
  have hpos : 0 < ‖(quadratic_map c)^[n] z‖ := by
    have hpos' : 0 < ‖(quadratic_map c)^[n] z‖ := lt_of_lt_of_le zero_lt_one h1
    exact hpos'
  have hpow :
      ‖(quadratic_map c)^[n] z‖ ^ ((1 : ℝ) / (2 : ℝ) ^ n) =
        Real.exp (((1 : ℝ) / (2 : ℝ) ^ n) * Real.log ‖(quadratic_map c)^[n] z‖) := by
    -- `x ^ y = exp (y * log x)` for `x > 0`
    simp [Real.rpow_def_of_pos hpos, mul_comm, one_div]
  have hpot := potential_seq_eq_log_norm_iterate c z n h1
  -- Assemble.
  calc
    ‖bottcher_root_seq c n z‖
        = ‖(quadratic_map c)^[n] z‖ ^ ((1 : ℝ) / (2 : ℝ) ^ n) := hnorm
    _ = Real.exp (((1 : ℝ) / (2 : ℝ) ^ n) * Real.log ‖(quadratic_map c)^[n] z‖) := hpow
    _ = Real.exp (Quadratic.potential_seq c z n) := by
          simp [hpot]

lemma norm_iterate_ge_one_of_escape
    (c z : ℂ) (hz : ‖z‖ > escape_bound c) :
    ∀ n, 1 ≤ ‖(quadratic_map c)^[n] z‖ := by
  intro n
  have hR : ‖z‖ > R c := lt_of_le_of_lt (escape_bound_ge_R c) hz
  have hge : ‖Quadratic.orbit c z n‖ ≥ ‖z‖ :=
    norm_orbit_ge_of_norm_ge_R c z n hR
  have horb : Quadratic.orbit c z n = (quadratic_map c)^[n] z := by
    rfl
  have hz1 : 1 ≤ ‖z‖ := by
    have hR2 : (2 : ℝ) ≤ escape_bound c := by
      have hR' := escape_bound_ge_R c
      have hR2' := R_ge_two c
      linarith
    linarith
  have hge' : ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ := by
    simpa [horb] using hge
  exact le_trans hz1 hge'

lemma bottcher_root_seq_norm_bounds_of_escape
    (c z : ℂ) (hz : ‖z‖ > escape_bound c) :
    let M : ℝ := 2 * ‖c‖ / (escape_bound c) ^ 2
    ∀ n,
      Real.exp (-(1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ ≤ ‖bottcher_root_seq c n z‖ ∧
        ‖bottcher_root_seq c n z‖ ≤ Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := by
  intro M n
  have hdist :
      dist (Quadratic.potential_seq c z n) (Quadratic.green_function c z) ≤
        (1 / 2 ^ n) * M := by
    have hesc0 : ‖Quadratic.orbit c z 0‖ > escape_bound c := by
      simpa [Quadratic.orbit] using hz
    have hesc : ‖Quadratic.orbit c z n‖ > escape_bound c := by
      exact norm_orbit_gt_escape_bound_of_ge c z 0 n (Nat.zero_le _) hesc0
    simpa [M] using
      (dist_potential_seq_green_function_le_of_escaping c z n hesc)
  have hpot_le :
      Quadratic.green_function c z - (1 / 2 ^ n) * M ≤ Quadratic.potential_seq c z n ∧
        Quadratic.potential_seq c z n ≤ Quadratic.green_function c z + (1 / 2 ^ n) * M := by
    have h' : |Quadratic.potential_seq c z n - Quadratic.green_function c z| ≤
        (1 / 2 ^ n) * M := by
      simpa [Real.dist_eq, abs_sub_comm] using hdist
    have h'' := abs_sub_le_iff.mp h'
    constructor <;> linarith
  have hnorm_root :
      ‖bottcher_root_seq c n z‖ = Real.exp (Quadratic.potential_seq c z n) := by
    have h1 := norm_iterate_ge_one_of_escape c z hz n
    exact bottcher_root_seq_norm_eq_exp_potential c z n h1
  have hnorm_bottcher :
      ‖Quadratic.bottcher_map c z‖ = Real.exp (Quadratic.green_function c z) :=
    Quadratic.norm_bottcher_eq_exp_green c z
  have hlow :
      Real.exp (Quadratic.green_function c z - (1 / 2 ^ n) * M) ≤
        Real.exp (Quadratic.potential_seq c z n) := by
    exact Real.exp_le_exp.mpr hpot_le.1
  have hhigh :
      Real.exp (Quadratic.potential_seq c z n) ≤
        Real.exp (Quadratic.green_function c z + (1 / 2 ^ n) * M) := by
    exact Real.exp_le_exp.mpr hpot_le.2
  have hlow' :
      Real.exp (-(1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ ≤
        ‖bottcher_root_seq c n z‖ := by
    calc
      Real.exp (-(1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖
          = Real.exp (Quadratic.green_function c z - (1 / 2 ^ n) * M) := by
              calc
                Real.exp (-(1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖
                    = Real.exp (Quadratic.green_function c z) * Real.exp (-(1 / 2 ^ n) * M) := by
                        simp [hnorm_bottcher, mul_comm]
                _ = Real.exp (Quadratic.green_function c z + (-(1 / 2 ^ n) * M)) := by
                        simp [Real.exp_add]
                _ = Real.exp (Quadratic.green_function c z - (1 / 2 ^ n) * M) := by
                        ring_nf
      _ ≤ Real.exp (Quadratic.potential_seq c z n) := hlow
      _ = ‖bottcher_root_seq c n z‖ := by
            symm; exact hnorm_root
  have hhigh' :
      ‖bottcher_root_seq c n z‖ ≤
        Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := by
    calc
      ‖bottcher_root_seq c n z‖
          = Real.exp (Quadratic.potential_seq c z n) := hnorm_root
      _ ≤ Real.exp (Quadratic.green_function c z + (1 / 2 ^ n) * M) := hhigh
      _ = Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := by
            calc
              Real.exp (Quadratic.green_function c z + (1 / 2 ^ n) * M)
                  = Real.exp (Quadratic.green_function c z) * Real.exp ((1 / 2 ^ n) * M) := by
                      simp [Real.exp_add]
              _ = Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := by
                      simp [hnorm_bottcher, mul_comm]
  exact ⟨hlow', hhigh'⟩

lemma bottcher_root_seq_norm_diff_bound_of_escape
    (c z : ℂ) (hz : ‖z‖ > escape_bound c) :
    let M : ℝ := 2 * ‖c‖ / (escape_bound c) ^ 2
    ∀ n,
      |‖bottcher_root_seq c n z‖ - ‖Quadratic.bottcher_map c z‖| ≤
        (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
  intro M n
  have hbound := (bottcher_root_seq_norm_bounds_of_escape c z hz) n
  have hlow : Real.exp (-(1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ ≤
      ‖bottcher_root_seq c n z‖ := hbound.1
  have hhigh : ‖bottcher_root_seq c n z‖ ≤
      Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := hbound.2
  have hpos : 0 ≤ ‖Quadratic.bottcher_map c z‖ := norm_nonneg _
  have hlow' : ‖Quadratic.bottcher_map c z‖ - ‖bottcher_root_seq c n z‖ ≤
      (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
    have hsum :
        ‖Quadratic.bottcher_map c z‖ - ‖bottcher_root_seq c n z‖ ≤
          ‖Quadratic.bottcher_map c z‖ + ‖bottcher_root_seq c n z‖ := by
      have hb : 0 ≤ ‖bottcher_root_seq c n z‖ := norm_nonneg _
      nlinarith
    have hle : ‖Quadratic.bottcher_map c z‖ + ‖bottcher_root_seq c n z‖ ≤
        (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
      have hle' : ‖bottcher_root_seq c n z‖ ≤
          Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := hhigh
      have hsum' : ‖Quadratic.bottcher_map c z‖ + ‖bottcher_root_seq c n z‖ ≤
          ‖Quadratic.bottcher_map c z‖ + Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := by
        nlinarith [hle']
      have hsum'' :
          ‖Quadratic.bottcher_map c z‖ + Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ =
            (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
        ring
      exact hsum'.trans_eq hsum''
    exact hsum.trans hle
  have hhigh' : ‖bottcher_root_seq c n z‖ - ‖Quadratic.bottcher_map c z‖ ≤
      (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
    have hsum :
        ‖bottcher_root_seq c n z‖ - ‖Quadratic.bottcher_map c z‖ ≤
          ‖bottcher_root_seq c n z‖ + ‖Quadratic.bottcher_map c z‖ := by
      have hb : 0 ≤ ‖Quadratic.bottcher_map c z‖ := norm_nonneg _
      nlinarith
    have hle : ‖bottcher_root_seq c n z‖ + ‖Quadratic.bottcher_map c z‖ ≤
        (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
      have hle' : ‖bottcher_root_seq c n z‖ ≤
          Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ := hhigh
      have hsum' : ‖bottcher_root_seq c n z‖ + ‖Quadratic.bottcher_map c z‖ ≤
          Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ + ‖Quadratic.bottcher_map c z‖ := by
        nlinarith [hle']
      have hsum'' :
          Real.exp ((1 / 2 ^ n) * M) * ‖Quadratic.bottcher_map c z‖ + ‖Quadratic.bottcher_map c z‖ =
            (Real.exp ((1 / 2 ^ n) * M) + 1) * ‖Quadratic.bottcher_map c z‖ := by
        ring
      exact hsum'.trans_eq hsum''
    exact hsum.trans hle
  exact abs_le.mpr ⟨by simpa [sub_eq_add_neg, add_comm] using hlow', hhigh'⟩


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

lemma eventually_atInfinity_norm_bottcher_map_ge (c : ℂ) (R : ℝ) :
    ∀ᶠ z in atInfinity, R ≤ ‖Quadratic.bottcher_map c z‖ := by
  let M : ℝ := 2 * ‖c‖ / (escape_bound c) ^ 2
  have hR : ∀ᶠ z in atInfinity,
      max (escape_bound c) (R * Real.exp M) < ‖z‖ :=
    eventually_atInfinity_norm_gt (max (escape_bound c) (R * Real.exp M))
  refine hR.mono ?_
  intro z hz
  have hzesc : ‖z‖ > escape_bound c := lt_of_le_of_lt (le_max_left _ _) hz
  have hbound := (bottcher_map_norm_bounds_of_escape c z hzesc)
  have hRle : R ≤ Real.exp (-M) * ‖z‖ := by
    have hzR : R * Real.exp M ≤ ‖z‖ := by
      exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
    have hpos : 0 ≤ Real.exp (-M) := by
      exact le_of_lt (Real.exp_pos _)
    have hzR' : R * Real.exp M * Real.exp (-M) ≤ ‖z‖ * Real.exp (-M) :=
      mul_le_mul_of_nonneg_right hzR hpos
    have hmul : Real.exp M * Real.exp (-M) = 1 := by
      calc
        Real.exp M * Real.exp (-M) = Real.exp (M + -M) := by
          simpa using (Real.exp_add M (-M)).symm
        _ = 1 := by simp
    calc
      R = R * (Real.exp M * Real.exp (-M)) := by
            simp [hmul]
      _ = R * Real.exp M * Real.exp (-M) := by ring
      _ ≤ ‖z‖ * Real.exp (-M) := hzR'
      _ = Real.exp (-M) * ‖z‖ := by ring
  exact hRle.trans hbound.1

lemma exists_norm_bottcher_map_ge_of_large_norm (c : ℂ) (R : ℝ) :
    ∃ S, ∀ z, S ≤ ‖z‖ → R ≤ ‖Quadratic.bottcher_map c z‖ := by
  have h := eventually_atInfinity_norm_bottcher_map_ge c R
  dsimp [atInfinity] at h
  have h' := (Filter.eventually_comap).1 h
  rcases (Filter.eventually_atTop.1 h') with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro z hz
  have := hS ‖z‖ hz z rfl
  simpa using this

lemma exists_norm_bottcher_map_gt_of_large_norm (c : ℂ) (R : ℝ) :
    ∃ S, ∀ z, S ≤ ‖z‖ → R < ‖Quadratic.bottcher_map c z‖ := by
  rcases exists_norm_bottcher_map_ge_of_large_norm c (R + 1) with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro z hz
  have h := hS z hz
  linarith

lemma preimage_closedBall_bounded (c : ℂ) (R : ℝ) :
    ∃ S, {z : ℂ | ‖Quadratic.bottcher_map c z‖ ≤ R} ⊆ {z : ℂ | ‖z‖ ≤ S} := by
  rcases exists_norm_bottcher_map_gt_of_large_norm c R with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro z hz
  by_contra h
  have hz' : S ≤ ‖z‖ := le_of_not_ge h
  have hgt : R < ‖Quadratic.bottcher_map c z‖ := hS z hz'
  exact (not_lt_of_ge (show R ≥ ‖Quadratic.bottcher_map c z‖ from hz)) hgt

lemma isCompact_preimage_closedBall_of_continuous
    {f : ℂ → ℂ} (R : ℝ) (hcont : Continuous f)
    (hbound : ∃ S, {z : ℂ | ‖f z‖ ≤ R} ⊆ {z : ℂ | ‖z‖ ≤ S}) :
    IsCompact {z : ℂ | ‖f z‖ ≤ R} := by
  rcases hbound with ⟨S, hS⟩
  have hclosed : IsClosed {z : ℂ | ‖f z‖ ≤ R} := by
    have hcont' : Continuous (fun z => ‖f z‖) := continuous_norm.comp hcont
    simpa using (isClosed_le hcont' continuous_const)
  have hsubset : {z : ℂ | ‖f z‖ ≤ R} ⊆ Metric.closedBall (0 : ℂ) S := by
    intro z hz
    have hz' : ‖z‖ ≤ S := hS hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hbounded : Bornology.IsBounded {z : ℂ | ‖f z‖ ≤ R} :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := S)).subset hsubset
  exact (Metric.isCompact_iff_isClosed_bounded).2 ⟨hclosed, hbounded⟩

lemma isCompact_preimage_closedBall_bottcher_map_of_closed
    (c : ℂ) (R : ℝ)
    (hclosed : IsClosed {z : ℂ | ‖Quadratic.bottcher_map c z‖ ≤ R}) :
    IsCompact {z : ℂ | ‖Quadratic.bottcher_map c z‖ ≤ R} := by
  rcases preimage_closedBall_bounded c R with ⟨S, hS⟩
  have hsubset : {z : ℂ | ‖Quadratic.bottcher_map c z‖ ≤ R} ⊆ Metric.closedBall (0 : ℂ) S := by
    intro z hz
    have hz' : ‖z‖ ≤ S := hS hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hbounded : Bornology.IsBounded {z : ℂ | ‖Quadratic.bottcher_map c z‖ ≤ R} :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := S)).subset hsubset
  exact (Metric.isCompact_iff_isClosed_bounded).2 ⟨hclosed, hbounded⟩

lemma bottcher_map_continuous_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    ContinuousOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  exact (bottcher_map_analytic_on_outside c hslit).continuousOn

lemma isCompact_preimage_of_isCompact
    {f : ℂ → ℂ} (hcont : Continuous f)
    (hbound : ∀ R, ∃ S, {z : ℂ | ‖f z‖ ≤ R} ⊆ {z : ℂ | ‖z‖ ≤ S})
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  rcases hK.isBounded.subset_closedBall (0 : ℂ) with ⟨R, hR⟩
  have hpre_ball : IsCompact {z : ℂ | ‖f z‖ ≤ R} :=
    isCompact_preimage_closedBall_of_continuous R hcont (hbound R)
  have hclosed : IsClosed (f ⁻¹' K) := hK.isClosed.preimage hcont
  have hsubset : f ⁻¹' K ⊆ {z : ℂ | ‖f z‖ ≤ R} := by
    intro z hz
    have hz' : f z ∈ Metric.closedBall (0 : ℂ) R := hR hz
    have : dist (f z) (0 : ℂ) ≤ R := by
      simpa [Metric.mem_closedBall] using hz'
    simpa [dist_eq_norm] using this
  exact hpre_ball.of_isClosed_subset hclosed hsubset

lemma bottcher_map_preimage_compact_of_isCompact
    (c : ℂ) (hcont : Continuous (Quadratic.bottcher_map c))
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact ((Quadratic.bottcher_map c) ⁻¹' K) := by
  exact isCompact_preimage_of_isCompact hcont
    (fun R => preimage_closedBall_bounded c R) hK

lemma bottcher_map_isProperMap_of_continuous
    (c : ℂ) (hcont : Continuous (Quadratic.bottcher_map c)) :
    IsProperMap (Quadratic.bottcher_map c) := by
  have hpre : ∀ ⦃K : Set ℂ⦄, IsCompact K →
      IsCompact ((Quadratic.bottcher_map c) ⁻¹' K) := by
    intro K hK
    exact bottcher_map_preimage_compact_of_isCompact c hcont hK
  exact (isProperMap_iff_isCompact_preimage (f := Quadratic.bottcher_map c)).2
    ⟨hcont, hpre⟩

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

lemma bottcher_root_seq_ratio_tendsto_of_bound
    (c : ℂ) (N : ℕ)
    (hbound :
      ∀ ε > 0, ∀ᶠ z in atInfinity, ‖bottcher_root_seq c N z - z‖ ≤ ε * ‖z‖) :
    Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have hgoal :
      Tendsto (fun z => ‖(bottcher_root_seq c N z - z) / z‖)
        atInfinity (𝓝 (0 : ℝ)) := by
    refine (tendsto_order.2 ?_)
    constructor
    · intro a ha
      have hnonneg : ∀ z, 0 ≤ ‖(bottcher_root_seq c N z - z) / z‖ := by
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
          ‖(bottcher_root_seq c N z - z) / z‖ =
            ‖bottcher_root_seq c N z - z‖ / ‖z‖ := by
        exact norm_div (bottcher_root_seq c N z - z) z
      have hle :
          ‖(bottcher_root_seq c N z - z) / z‖ ≤ a / 2 := by
        have hle' :
            ‖bottcher_root_seq c N z - z‖ / ‖z‖ ≤ a / 2 := by
          have : ‖bottcher_root_seq c N z - z‖ ≤ (a / 2) * ‖z‖ := hbd
          exact (div_le_iff₀ hzpos).2 (by simpa [mul_comm] using this)
        simpa [hnorm] using hle'
      have hlt : a / 2 < a := by
        nlinarith
      exact lt_of_le_of_lt hle hlt
  have hne : ∀ᶠ z in atInfinity, z ≠ 0 := by
    have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
      (eventually_atInfinity_norm_gt (0 : ℝ))
    exact hpos.mono (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
  have hsplit :
      ∀ᶠ z in atInfinity,
        ‖(bottcher_root_seq c N z - z) / z‖ =
          ‖bottcher_root_seq c N z / z - (1 : ℂ)‖ := by
    refine hne.mono ?_
    intro z hz
    have hsplit' :
        bottcher_root_seq c N z / z - (1 : ℂ) =
          (bottcher_root_seq c N z - z) / z := by
      field_simp [hz]
    simp [hsplit']
  have hgoal' :
      Tendsto (fun z => ‖bottcher_root_seq c N z / z - (1 : ℂ)‖)
        atInfinity (𝓝 (0 : ℝ)) := by
    exact (tendsto_congr' hsplit).1 hgoal
  simpa using hgoal'

lemma bottcher_root_seq_zero_error_bound (c : ℂ) :
    ∀ ε > 0, ∀ᶠ z in atInfinity, ‖bottcher_root_seq c 0 z - z‖ ≤ ε * ‖z‖ := by
  intro ε hε
  refine Filter.Eventually.of_forall ?_
  intro z
  have hnonneg : 0 ≤ ε * ‖z‖ :=
    mul_nonneg (le_of_lt hε) (norm_nonneg _)
  simpa [bottcher_root_seq] using hnonneg

lemma bottcher_root_seq_ratio_tendsto_atInfinity_zero (c : ℂ) :
    Tendsto (fun z => bottcher_root_seq c 0 z / z) atInfinity (𝓝 (1 : ℂ)) := by
  have hbound : ∀ ε > 0, ∀ᶠ z in atInfinity,
      ‖bottcher_root_seq c 0 z - z‖ ≤ ε * ‖z‖ :=
    bottcher_root_seq_zero_error_bound c
  exact bottcher_root_seq_ratio_tendsto_of_bound c 0 hbound

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
    (c : ℂ) (R : ℝ) (hRpos : 0 < R)
    (hannulus :
      ∀ S, R ≤ S →
        TendstoUniformlyOn (bottcher_root_seq c) (Quadratic.bottcher_map c) atTop
          (exterior_annulus R S))
    (htail :
      ∀ ε > 0, ∃ S ≥ R, ∀ n z, S ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε * ‖z‖) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε * ‖z‖ := by
  intro ε hε
  rcases htail ε hε with ⟨S, hSR, htail'⟩
  have hann := hannulus S hSR
  rcases uniform_bound_of_tendstoUniformlyOn (F := bottcher_root_seq c)
    (f := Quadratic.bottcher_map c) (s := exterior_annulus R S) hann (ε * R)
    (mul_pos hε hRpos) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn z hz
  by_cases hzs : ‖z‖ ≤ S
  · have hz' : z ∈ exterior_annulus R S := ⟨hz, hzs⟩
    have h := hN n hn z hz'
    have hle : ε * R ≤ ε * ‖z‖ :=
      mul_le_mul_of_nonneg_left hz (le_of_lt hε)
    exact h.trans hle
  · have hzs' : S ≤ ‖z‖ := le_of_not_ge hzs
    exact htail' n z hzs'

lemma bottcher_root_seq_error_bound_of_large_R
    (c : ℂ) (R : ℝ) (hR : ‖c‖ + 2 ≤ R)
    (htail :
      ∀ ε > 0, ∃ S ≥ R, ∀ n z, S ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε * ‖z‖) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - bottcher_root_seq c n z‖ ≤ ε * ‖z‖ := by
  have hRpos : 0 < R := by
    have hcn : (0 : ℝ) ≤ ‖c‖ := by exact norm_nonneg _
    linarith
  refine bottcher_root_seq_error_bound_of_annulus_and_tail c R hRpos ?_ htail
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

def bottcher_tail_bound_at (c : ℂ) (R : ℝ) (N : ℕ) : Prop :=
  ∀ ε > 0, ∃ S ≥ R, ∀ z, S ≤ ‖z‖ →
    ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖

def bottcher_tail_bound (c : ℂ) (R : ℝ) : Prop :=
  ∃ N, bottcher_tail_bound_at c R N

lemma bottcher_tail_bound_at_of_exterior
    (c : ℂ) (R : ℝ) (N : ℕ)
    (hR :
      ∀ ε > 0, ∃ S, ∀ z, S ≤ ‖z‖ →
        ‖Quadratic.bottcher_map c z - bottcher_root_seq c N z‖ ≤ ε * ‖z‖) :
    bottcher_tail_bound_at c R N := by
  intro ε hε
  rcases hR ε hε with ⟨S, hS⟩
  refine ⟨max S R, le_max_right _ _, ?_⟩
  intro z hz
  have hz' : S ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  exact hS z hz'

lemma bottcher_normalized_at_infty_of_large_R
    (c : ℂ) (R : ℝ) (N : ℕ)
    (hroot : Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)))
    (htail : bottcher_tail_bound_at c R N) :
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
    exact htail' z (le_of_lt hz)
  exact bottcher_normalized_at_infty_of_root_seq_bound c N hroot hbound'

theorem bottcher_normalized_at_infty_of_tail_bound_at
    (c : ℂ) (R : ℝ) (N : ℕ)
    (hroot : Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ)))
    (htail : bottcher_tail_bound_at c R N) :
    bottcher_normalized_at_infty c :=
  bottcher_normalized_at_infty_of_large_R c R N hroot htail

theorem bottcher_normalized_at_infty_of_tail_bound
    (c : ℂ) (R : ℝ)
    (htail :
      ∃ N, bottcher_tail_bound_at c R N ∧
        Tendsto (fun z => bottcher_root_seq c N z / z) atInfinity (𝓝 (1 : ℂ))) :
    bottcher_normalized_at_infty c := by
  rcases htail with ⟨N, htailN, hrootN⟩
  exact bottcher_normalized_at_infty_of_tail_bound_at c R N hrootN htailN

theorem bottcher_normalized_at_infty_of_tail_bound_zero
    (c : ℂ) (R : ℝ)
    (htail : bottcher_tail_bound_at c R 0) :
    bottcher_normalized_at_infty c := by
  refine bottcher_normalized_at_infty_of_tail_bound_at c R 0 ?_ htail
  exact bottcher_root_seq_ratio_tendsto_atInfinity_zero c

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

lemma bottcher_map_local_inj_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hinj : Set.InjOn (Quadratic.bottcher_map c) (outside_disk c)) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → ∃ s ∈ 𝓝 z, Set.InjOn (Quadratic.bottcher_map c) s := by
  intro z hz
  have hf : AnalyticAt ℂ (Quadratic.bottcher_map c) z :=
    (bottcher_map_analytic_on_outside c hslit) z (by simpa using hz)
  have hderiv : deriv (Quadratic.bottcher_map c) z ≠ 0 :=
    bottcher_map_deriv_ne_zero_on_outside c hslit hinj z hz
  exact injOn_nhds_of_analyticAt hf hderiv

lemma isLocalHomeomorphOn_of_analytic_deriv_ne_zero
    {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ z ∈ s, AnalyticAt ℂ f z) (hderiv : ∀ z ∈ s, deriv f z ≠ 0) :
    IsLocalHomeomorphOn f s := by
  intro z hz
  have hstrict : HasStrictDerivAt f (deriv f z) z := (hf z hz).hasStrictDerivAt
  have hstrict' :=
    HasStrictDerivAt.hasStrictFDerivAt_equiv (f := f) (f' := deriv f z) hstrict (hderiv z hz)
  refine ⟨hstrict'.toOpenPartialHomeomorph f, ?_, ?_⟩
  · exact hstrict'.mem_toOpenPartialHomeomorph_source
  · simp [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]

lemma bottcher_map_isLocalHomeomorphOn_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hinj : Set.InjOn (Quadratic.bottcher_map c) (outside_disk c)) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  refine isLocalHomeomorphOn_of_analytic_deriv_ne_zero ?_ ?_
  · intro z hz
    exact (bottcher_map_analytic_on_outside c hslit) z (by simpa using hz)
  · intro z hz
    exact bottcher_map_deriv_ne_zero_on_outside c hslit hinj z (by simpa using hz)

lemma bottcher_map_isLocalHomeomorphOn_outside_of_deriv_ne_zero
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hderiv : ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  refine isLocalHomeomorphOn_of_analytic_deriv_ne_zero ?_ ?_
  · intro z hz
    exact (bottcher_map_analytic_on_outside c hslit) z (by simpa using hz)
  · intro z hz
    exact hderiv z (by simpa using hz)

lemma isOpenMap_of_analytic_deriv_ne_zero
    {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (hderiv : ∀ z, deriv f z ≠ 0) :
    IsOpenMap f := by
  have hstrict : ∀ z, HasStrictDerivAt f (deriv f z) z :=
    fun z => (hf z).hasStrictDerivAt
  exact (isOpenMap_of_hasStrictDerivAt (f := f)
    (f' := fun z => deriv f z) hstrict hderiv)

lemma norm_deriv_sub_id_le_of_sphere_bound
    {f : ℂ → ℂ} {z₀ : ℂ} {R C : ℝ}
    (hR : 0 < R) (hDiff : DiffContOnCl ℂ f (Metric.ball z₀ R))
    (hC : ∀ z ∈ Metric.sphere z₀ R, ‖f z - z‖ ≤ C) :
    ‖deriv f z₀ - 1‖ ≤ C / R := by
  have h_id : DiffContOnCl ℂ (fun z : ℂ => z) (Metric.ball z₀ R) := by
    simpa using (Differentiable.diffContOnCl (f := fun z : ℂ => z)
      (s := Metric.ball z₀ R) (differentiable_id : Differentiable ℂ fun z : ℂ => z))
  have hDiff' : DiffContOnCl ℂ (fun z : ℂ => f z - z) (Metric.ball z₀ R) :=
    hDiff.sub h_id
  have hC' : ∀ z ∈ Metric.sphere z₀ R, ‖(fun z => f z - z) z‖ ≤ C := by
    intro z hz
    simpa using hC z hz
  have hderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z₀) (R := R)
    (f := fun z : ℂ => f z - z) hR hDiff' hC'
  have hdf : DifferentiableAt ℂ f z₀ :=
    (hDiff.differentiableAt Metric.isOpen_ball (Metric.mem_ball_self hR))
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) z₀ :=
    differentiable_id.differentiableAt
  have hderiv' : deriv (fun z : ℂ => f z - z) z₀ = deriv f z₀ - 1 := by
    simpa using (deriv_fun_sub hdf hid)
  have hle' : ‖deriv f z₀ - 1‖ ≤ C / R := by
    simpa [hderiv'] using hderiv
  exact hle'

lemma deriv_ne_zero_of_sphere_bound
    {f : ℂ → ℂ} {z₀ : ℂ} {R C : ℝ}
    (hR : 0 < R) (hDiff : DiffContOnCl ℂ f (Metric.ball z₀ R))
    (hC : ∀ z ∈ Metric.sphere z₀ R, ‖f z - z‖ ≤ C)
    (hC' : C / R < 1) :
    deriv f z₀ ≠ 0 := by
  have hle := norm_deriv_sub_id_le_of_sphere_bound (f := f) (z₀ := z₀)
    (R := R) (C := C) hR hDiff hC
  intro hzero
  have hnorm : ‖deriv f z₀ - 1‖ = 1 := by
    simp [hzero]
  have hge : (1 : ℝ) ≤ C / R := by
    simpa [hnorm] using hle
  exact (not_lt_of_ge hge) hC'

lemma bottcher_map_minus_id_bound_of_normalized
    (c : ℂ) (hnorm : bottcher_normalized_at_infty c) :
    ∀ ε > 0, ∃ R, ∀ z, R ≤ ‖z‖ →
      ‖Quadratic.bottcher_map c z - z‖ ≤ ε * ‖z‖ := by
  intro ε hε
  have h0 :
      Tendsto (fun z => ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖) atInfinity
        (𝓝 (0 : ℝ)) := by
    have h := (bottcher_normalized_at_infty_iff c).1 hnorm
    simpa using h
  have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have hε' : ∀ᶠ z in atInfinity,
      ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖ < ε := by
    simpa [Metric.ball, Set.mem_setOf_eq] using (tendsto_def.1 h0 _ hball)
  have hε'' := (Filter.eventually_comap).1 hε'
  rcases (Filter.eventually_atTop.1 hε'') with ⟨R, hR⟩
  let R' := max R 1
  refine ⟨R', ?_⟩
  intro z hz
  have hzR : R ≤ ‖z‖ := le_trans (le_max_left _ _) hz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (le_trans (le_max_right _ _) hz)
  have hne : z ≠ 0 := by
    exact (norm_ne_zero_iff).1 (ne_of_gt hzpos)
  have hratio : ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖ < ε := hR ‖z‖ hzR z rfl
  have hmul :
      Quadratic.bottcher_map c z - z =
        z * ((Quadratic.bottcher_map c z) / z - (1 : ℂ)) := by
    have hmul1 : z * (Quadratic.bottcher_map c z / z) = Quadratic.bottcher_map c z := by
      calc
        z * (Quadratic.bottcher_map c z / z)
            = z * (Quadratic.bottcher_map c z * z⁻¹) := by
                simp [div_eq_mul_inv]
        _ = Quadratic.bottcher_map c z * (z * z⁻¹) := by
                ring
        _ = Quadratic.bottcher_map c z := by
                simp [hne]
    calc
      Quadratic.bottcher_map c z - z
          = z * (Quadratic.bottcher_map c z / z) - z := by
              simp [hmul1]
      _ = z * ((Quadratic.bottcher_map c z) / z - (1 : ℂ)) := by
              ring
  have hle : ‖Quadratic.bottcher_map c z - z‖ ≤ ε * ‖z‖ := by
    have hle' : ‖z * ((Quadratic.bottcher_map c z) / z - (1 : ℂ))‖ ≤ ε * ‖z‖ := by
      have hle'' : ‖z‖ * ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖ ≤
          ‖z‖ * ε := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hratio) (norm_nonneg _)
      have hle''' : ‖z‖ * ε = ε * ‖z‖ := by ring
      have hle'''' : ‖z‖ * ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖ ≤ ε * ‖z‖ :=
        hle''.trans_eq hle'''
      calc
        ‖z * ((Quadratic.bottcher_map c z) / z - (1 : ℂ))‖
            = ‖z‖ * ‖(Quadratic.bottcher_map c z) / z - (1 : ℂ)‖ := by
                exact (norm_mul z ((Quadratic.bottcher_map c z) / z - (1 : ℂ)))
        _ ≤ ε * ‖z‖ := hle''''
    have hle'' : ‖Quadratic.bottcher_map c z - z‖ ≤ ε * ‖z‖ := by
      simpa [hmul] using hle'
    exact hle''
  exact hle

lemma isOpen_image_of_isLocalHomeomorphOn
    {f : ℂ → ℂ} {s : Set ℂ} (hlocal : IsLocalHomeomorphOn f s) :
    ∀ t ⊆ s, IsOpen t → IsOpen (f '' t) := by
  intro t ht htop
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨U, hU, hEmb⟩ :=
    (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict (f := f) (s := s)).1 hlocal x (ht hx)
  have hOpenMap : IsOpenMap (U.restrict f) := hEmb.isOpenMap
  have hUopen : IsOpen ((Subtype.val : U → ℂ) ⁻¹' t) := by
    exact htop.preimage continuous_subtype_val
  have hxU : x ∈ U := by
    have hxint : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
    exact interior_subset hxint
  have hmem : (⟨x, hxU⟩ : U) ∈ (Subtype.val : U → ℂ) ⁻¹' t := by
    simpa using hx
  have hnhds : (U.restrict f) '' ((Subtype.val : U → ℂ) ⁻¹' t) ∈ 𝓝 (f x) := by
    have hopen : IsOpen ((U.restrict f) '' ((Subtype.val : U → ℂ) ⁻¹' t)) :=
      hOpenMap _ hUopen
    exact hopen.mem_nhds ⟨⟨x, hxU⟩, hmem, rfl⟩
  refine mem_of_superset hnhds ?_
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z.1, hz, rfl⟩

lemma bottcher_map_isOpen_on_outside_of_deriv_ne_zero
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hderiv : ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0) :
    ∀ t ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2}, IsOpen t →
      IsOpen (Quadratic.bottcher_map c '' t) := by
  intro t ht htop
  have hlocal := bottcher_map_isLocalHomeomorphOn_outside_of_deriv_ne_zero c hslit hderiv
  exact isOpen_image_of_isLocalHomeomorphOn hlocal t ht htop

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

lemma slitPlaneRot_eq_slitPlane_of_exp_eq_one (θ : ℝ)
    (hθ : Complex.exp (Complex.I * θ) = 1) :
    slitPlaneRot θ = Complex.slitPlane := by
  have hneg : Complex.exp (-Complex.I * θ) = 1 := by
    calc
      Complex.exp (-Complex.I * θ)
          = Complex.exp (-(Complex.I * θ)) := by ring_nf
      _ = (Complex.exp (Complex.I * θ))⁻¹ := by
            simp [Complex.exp_neg]
      _ = 1 := by simp [hθ]
  have hneg' : Complex.exp (-(Complex.I * θ)) = 1 := by
    calc
      Complex.exp (-(Complex.I * θ)) = Complex.exp (-Complex.I * θ) := by ring_nf
      _ = 1 := hneg
  ext z
  simp [slitPlaneRot, hneg']

lemma slit_orbit_rot_eq_slit_orbit_of_exp_eq_one (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (Complex.I * θ) = 1) :
    slit_orbit_rot c θ = slit_orbit c := by
  ext z
  simp [slit_orbit_rot, slit_orbit, slitPlaneRot_eq_slitPlane_of_exp_eq_one θ hθ]

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

noncomputable def quadratic_map_rot_param (c : ℂ) (θ : ℝ) (n : ℕ) : ℂ :=
  c * Complex.exp (-Complex.I * θ * (2 : ℂ) ^ n)

noncomputable def quadratic_map_rot_iter (c : ℂ) (θ : ℝ) : ℕ → ℂ → ℂ
  | 0, z => z
  | n + 1, z => quadratic_map (quadratic_map_rot_param c θ (n + 1))
      (quadratic_map_rot_iter c θ n z)

lemma quadratic_map_rotate_iter (c : ℂ) (θ : ℝ) (n : ℕ) (z : ℂ) :
    (quadratic_map c)^[n] (z * Complex.exp (Complex.I * θ)) =
      (quadratic_map_rot_iter c θ n z) * Complex.exp (Complex.I * θ * (2 : ℂ) ^ n) := by
  induction n with
  | zero =>
      simp [quadratic_map_rot_iter]
  | succ n ih =>
      have hpow : (2 : ℂ) ^ (n + 1) = (2 : ℂ) ^ n * 2 := by
        simp [pow_succ, mul_comm]
      have hExp :
          Complex.exp (Complex.I * θ * (2 : ℂ) ^ n * 2) =
            Complex.exp (Complex.I * θ * (2 : ℂ) ^ (n + 1)) := by
        simp [hpow, mul_assoc]
      calc
        (quadratic_map c)^[n + 1] (z * Complex.exp (Complex.I * θ))
            = quadratic_map c ((quadratic_map c)^[n] (z * Complex.exp (Complex.I * θ))) := by
                simpa using
                  (Function.iterate_succ_apply' (f := quadratic_map c) n
                    (z * Complex.exp (Complex.I * θ)))
        _ = quadratic_map c
              ((quadratic_map_rot_iter c θ n z) *
                Complex.exp (Complex.I * θ * (2 : ℂ) ^ n)) := by
                simp [ih]
        _ =
            (quadratic_map (quadratic_map_rot_param c θ (n + 1)) (quadratic_map_rot_iter c θ n z)) *
              Complex.exp (Complex.I * θ * (2 : ℂ) ^ n * 2) := by
                simpa [quadratic_map_rot_param, hpow, mul_assoc, mul_left_comm, mul_comm] using
                  (quadratic_map_rotate c (θ * (2 : ℝ) ^ n) (quadratic_map_rot_iter c θ n z))
        _ =
            (quadratic_map_rot_iter c θ (n + 1) z) *
              Complex.exp (Complex.I * θ * (2 : ℂ) ^ (n + 1)) := by
                simp [quadratic_map_rot_iter, hExp]

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

lemma local_slit_subset_ball (z₀ : ℂ) (ε : ℝ) :
    local_slit z₀ ε ⊆ {z : ℂ | dist z z₀ < ε} := by
  intro z hz
  exact hz.1

def slit_orbit_prefix (c : ℂ) (N : ℕ) : Set ℂ :=
  {z | ∀ n ≤ N, (quadratic_map c)^[n] z ∈ Complex.slitPlane}

lemma exists_local_slit_subset_slit_orbit_of_ball
    (c z₀ : ℂ)
    (hball : ∃ ε > 0, ∀ z, dist z z₀ < ε → z ∈ slit_orbit c) :
    ∃ ε > 0, local_slit z₀ ε ⊆ slit_orbit c := by
  rcases hball with ⟨ε, εpos, hε⟩
  refine ⟨ε, εpos, ?_⟩
  intro z hz
  exact hε z (local_slit_subset_ball z₀ ε hz)

lemma exists_local_slit_subset_slit_orbit_of_mem_nhds
    (c z₀ : ℂ) (hz₀ : slit_orbit c ∈ 𝓝 z₀) :
    ∃ ε > 0, local_slit z₀ ε ⊆ slit_orbit c := by
  rcases Metric.mem_nhds_iff.mp hz₀ with ⟨ε, εpos, hε⟩
  refine exists_local_slit_subset_slit_orbit_of_ball c z₀ ?_
  refine ⟨ε, εpos, ?_⟩
  intro z hz
  exact hε hz

lemma exists_local_slit_subset_basin_of_mem_nhds
    (c z₀ : ℂ) (hz₀ : Quadratic.basin_of_infinity c ∈ 𝓝 z₀) :
    ∃ ε > 0, local_slit z₀ ε ⊆ Quadratic.basin_of_infinity c := by
  rcases Metric.mem_nhds_iff.mp hz₀ with ⟨ε, εpos, hε⟩
  refine ⟨ε, εpos, ?_⟩
  intro z hz
  exact hε (local_slit_subset_ball z₀ ε hz)

lemma exists_local_slit_subset_slit_orbit_basin_of_mem_nhds
    (c z₀ : ℂ)
    (hslit : slit_orbit c ∈ 𝓝 z₀)
    (hbasin : Quadratic.basin_of_infinity c ∈ 𝓝 z₀) :
    ∃ ε > 0, local_slit z₀ ε ⊆ slit_orbit c ∩ Quadratic.basin_of_infinity c := by
  rcases exists_local_slit_subset_slit_orbit_of_mem_nhds c z₀ hslit with ⟨ε1, ε1pos, hε1⟩
  rcases exists_local_slit_subset_basin_of_mem_nhds c z₀ hbasin with ⟨ε2, ε2pos, hε2⟩
  let ε := min ε1 ε2
  have εpos : 0 < ε := lt_min ε1pos ε2pos
  refine ⟨ε, εpos, ?_⟩
  intro z hz
  have hz1 : z ∈ local_slit z₀ ε1 := by
    refine ⟨?_, hz.2⟩
    have hzdist : dist z z₀ < ε := by
      simpa using hz.1
    exact lt_of_lt_of_le hzdist (min_le_left _ _)
  have hz2 : z ∈ local_slit z₀ ε2 := by
    refine ⟨?_, hz.2⟩
    have hzdist : dist z z₀ < ε := by
      simpa using hz.1
    exact lt_of_lt_of_le hzdist (min_le_right _ _)
  exact ⟨hε1 hz1, hε2 hz2⟩


lemma bottcher_map_analytic_on_local_slit
    (c z₀ : ℂ) (ε : ℝ)
    (hslit : local_slit z₀ ε ⊆ slit_orbit c)
    (hbasin : local_slit z₀ ε ⊆ Quadratic.basin_of_infinity c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) (local_slit z₀ ε) := by
  have hopen : IsOpen (local_slit z₀ ε) := local_slit_isOpen z₀ ε
  exact bottcher_map_analyticOnNhd_open c (local_slit z₀ ε) hopen hslit hbasin

lemma bottcher_map_analytic_on_local_slit_of_mem_nhds
    (c z₀ : ℂ)
    (hslit : slit_orbit c ∈ 𝓝 z₀)
    (hbasin : Quadratic.basin_of_infinity c ∈ 𝓝 z₀) :
    ∃ ε > 0, AnalyticOnNhd ℂ (Quadratic.bottcher_map c) (local_slit z₀ ε) := by
  rcases exists_local_slit_subset_slit_orbit_basin_of_mem_nhds c z₀ hslit hbasin with
    ⟨ε, εpos, hsub⟩
  refine ⟨ε, εpos, ?_⟩
  have hslit' : local_slit z₀ ε ⊆ slit_orbit c := fun z hz => (hsub hz).1
  have hbasin' : local_slit z₀ ε ⊆ Quadratic.basin_of_infinity c := fun z hz => (hsub hz).2
  exact bottcher_map_analytic_on_local_slit c z₀ ε hslit' hbasin'

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

lemma exists_local_slit_subset_slit_orbit_prefix
    (c z₀ : ℂ) (N : ℕ) (hz₀ : z₀ ∈ slit_orbit c) :
    ∃ ε > 0, local_slit z₀ ε ⊆ slit_orbit_prefix c N := by
  rcases exists_ball_subset_slit_orbit_prefix c z₀ N hz₀ with ⟨ε, εpos, hε⟩
  refine ⟨ε, εpos, ?_⟩
  intro z hz
  exact hε z (local_slit_subset_ball z₀ ε hz)

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
