import Mlc.Quadratic.Complex.Bottcher.BottcherOutsideOutline
import Mlc.Quadratic.Complex.Bottcher.BottcherAnalyticInjective
import Mlc.Quadratic.Complex.Bottcher.BottcherCpowSlit
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMOutsideOutline
import Mlc.Quadratic.Complex.InverseBranchQuadratic
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.DiscreteSubset
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
  Goal: `Tendsto (fun z => ‖bottcher_map c z‖ / ‖z‖) atInfinity (𝓝 1)`.
  Use: Green function asymptotics at infinity.
  (The full complex ratio requires a different normalization for `bottcher_map`.)

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
  have hz' : z ∈ {w : ℂ | ‖w‖ ≥ ‖c‖ + 2} := by
    have : ‖z‖ > ‖c‖ + 2 := by simpa using hz
    exact le_of_lt this
  simpa [outside_disk, basin_of_infinity] using (escaping_set_contains_large_ball c hz')

lemma large_norm_mem_outside_disk (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    z ∈ outside_disk c := by
  have hz' : z ∈ {w : ℂ | ‖w‖ ≥ ‖c‖ + 2} := by
    simpa [Set.mem_setOf_eq] using hz
  simpa [outside_disk, basin_of_infinity] using (escaping_set_contains_large_ball c hz')

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


-- TODO (strong normalization): show
-- `Tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 1)`.
-- This is not expected for the current `bottcher_map` definition (e.g. `c = 0` gives
-- the radial normalization), but can hold on argument sectors.

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

lemma tendsto_norm_quadratic_iter_div_pow_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto (fun z => ‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) atInfinity (𝓝 (1 : ℝ)) := by
  have h := tendsto_quadratic_iter_div_pow_atInfinity c N
  have hnorm :
      Tendsto (fun z => ‖(quadratic_map c)^[N] z / z ^ (2 ^ N)‖) atInfinity (𝓝 (‖(1 : ℂ)‖)) :=
    (continuous_norm.tendsto (1 : ℂ)).comp h
  simpa [norm_div, norm_pow] using hnorm

lemma tendsto_log_norm_quadratic_iter_div_pow_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto (fun z => Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)))
      atInfinity (𝓝 (0 : ℝ)) := by
  have h := tendsto_norm_quadratic_iter_div_pow_atInfinity c N
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h
  simpa using hlog

lemma tendsto_potential_seq_minus_log_norm_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto
        (fun z =>
          (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ - Real.log ‖z‖)
        atInfinity (𝓝 (0 : ℝ)) := by
  have hlog := tendsto_log_norm_quadratic_iter_div_pow_atInfinity c N
  have hne : ∀ᶠ z in atInfinity, ‖z‖ ≠ 0 := by
    have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
      eventually_atInfinity_norm_gt (0 : ℝ)
    exact hpos.mono (fun _ hz => ne_of_gt hz)
  have hne' : ∀ᶠ z in atInfinity, ‖(quadratic_map c)^[N] z‖ ≠ 0 := by
    have hA : ∀ᶠ z in atInfinity, (quadratic_map c)^[N] z ≠ 0 :=
      eventually_atInfinity_iter_ne_zero c N
    exact hA.mono (fun _ hz => by simpa using (norm_ne_zero_iff.mpr hz))
  have hsplit :
      ∀ᶠ z in atInfinity,
        (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ - Real.log ‖z‖ =
          (1 / (2 : ℝ) ^ N) *
            Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) := by
    refine (hne'.and hne).mono ?_
    intro z hz
    rcases hz with ⟨hne', hne⟩
    have hlogdiv :
        Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) =
          Real.log ‖(quadratic_map c)^[N] z‖ - (2 ^ N : ℝ) * Real.log ‖z‖ := by
      have hlogdiv' :
          Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) =
            Real.log ‖(quadratic_map c)^[N] z‖ - Real.log (‖z‖ ^ (2 ^ N)) := by
        exact (Real.log_div hne' (pow_ne_zero (2 ^ N) hne))
      have hlogpow :
          Real.log (‖z‖ ^ (2 ^ N)) = (2 ^ N : ℕ) * Real.log ‖z‖ := by
        exact (Real.log_pow ‖z‖ (2 ^ N))
      have hlogpow' :
          Real.log (‖z‖ ^ (2 ^ N)) = (2 ^ N : ℝ) * Real.log ‖z‖ := by
        simp [hlogpow]
      calc
        Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N))
            = Real.log ‖(quadratic_map c)^[N] z‖ - Real.log (‖z‖ ^ (2 ^ N)) := hlogdiv'
        _ = Real.log ‖(quadratic_map c)^[N] z‖ - (2 ^ N : ℝ) * Real.log ‖z‖ := by
              simp [hlogpow']
    have hcoef : (1 / (2 : ℝ) ^ N) * ((2 ^ N : ℝ) * Real.log ‖z‖) = Real.log ‖z‖ := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have hpow : (1 / (2 : ℝ) ^ N) * (2 ^ N : ℝ) = 1 := by
        calc
          (1 / (2 : ℝ) ^ N) * (2 ^ N : ℝ) = ((2 : ℝ) ^ N)⁻¹ * (2 ^ N : ℝ) := by
              simp [one_div]
          _ = 1 := by
              simp [h2]
      calc
        (1 / (2 : ℝ) ^ N) * ((2 ^ N : ℝ) * Real.log ‖z‖)
            = ((1 / (2 : ℝ) ^ N) * (2 ^ N : ℝ)) * Real.log ‖z‖ := by
                ring
        _ = Real.log ‖z‖ := by
                simp
    calc
      (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ - Real.log ‖z‖
          = (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ -
              (1 / (2 : ℝ) ^ N) * ((2 ^ N : ℝ) * Real.log ‖z‖) := by
                simp
      _ = (1 / (2 : ℝ) ^ N) *
            (Real.log ‖(quadratic_map c)^[N] z‖ - (2 ^ N : ℝ) * Real.log ‖z‖) := by
            ring
      _ = (1 / (2 : ℝ) ^ N) *
            Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) := by
            simp [hlogdiv]
      _ = (1 / (2 : ℝ) ^ N) *
            Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) := by
            simp [hlogdiv]
  have hmul :
      Tendsto
          (fun z =>
            (1 / (2 : ℝ) ^ N) *
              Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)))
          atInfinity (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hlog)
  exact (tendsto_congr' hsplit).2 hmul

lemma tendsto_green_function_minus_log_norm_atInfinity (c : ℂ) :
    Tendsto (fun z => Quadratic.green_function c z - Real.log ‖z‖) atInfinity (𝓝 (0 : ℝ)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have hgoal :
      Tendsto (fun z => |Quadratic.green_function c z - Real.log ‖z‖|)
        atInfinity (𝓝 (0 : ℝ)) := by
    refine (tendsto_order.2 ?_)
    constructor
    · intro a ha
      have hnonneg : ∀ z, 0 ≤ |Quadratic.green_function c z - Real.log ‖z‖| := by
        intro z
        exact abs_nonneg _
      exact Filter.Eventually.of_forall (fun z => lt_of_lt_of_le ha (hnonneg z))
    · intro a ha
      have ha' : 0 < a / 2 := by
        nlinarith
      let M : ℝ := 2 * ‖c‖ / (escape_bound c) ^ 2
      have hpow0 :
          Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (1 / 2))
          (by norm_num : (1 / 2 : ℝ) < 1)
      have hpow :
          Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * M) atTop (𝓝 (0 : ℝ)) :=
        by
          simpa using (hpow0.mul tendsto_const_nhds)
      have hball : Metric.ball (0 : ℝ) (a / 2) ∈ 𝓝 (0 : ℝ) :=
        Metric.ball_mem_nhds _ ha'
      have hN' := (tendsto_def.1 hpow _ hball)
      rcases (Filter.eventually_atTop.1 hN') with ⟨N, hN⟩
      have hNbound : (2 ^ N : ℝ)⁻¹ * M < a / 2 := by
        have h := hN N (le_rfl)
        have hM : 0 ≤ M := by
          have hnum : 0 ≤ 2 * ‖c‖ := by
            nlinarith [norm_nonneg c]
          have hden : 0 ≤ (escape_bound c) ^ 2 := by
            nlinarith
          exact div_nonneg hnum hden
        have h' : |(1 / 2 : ℝ) ^ N| * |M| < a / 2 := by
          simpa [Metric.ball, Set.mem_setOf_eq, Real.dist_eq, abs_mul] using h
        have h'' : |(1 / 2 : ℝ) ^ N| * M < a / 2 := by
          simpa [abs_of_nonneg hM] using h'
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ N := by
          exact pow_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)) _
        have hpow_abs : |(1 / 2 : ℝ) ^ N| = (1 / 2 : ℝ) ^ N :=
          abs_of_nonneg hpow_nonneg
        have h''' : (1 / 2 : ℝ) ^ N * M < a / 2 := by
          simpa [hpow_abs] using h''
        -- rewrite `(1/2)^N` as `(2^N)⁻¹`
        simpa [one_div, inv_pow] using h'''
      have hpot : ∀ᶠ z in atInfinity,
          |(1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ - Real.log ‖z‖| < a / 2 := by
        have hpot' := tendsto_potential_seq_minus_log_norm_atInfinity c N
        have hball' : Metric.ball (0 : ℝ) (a / 2) ∈ 𝓝 (0 : ℝ) :=
          Metric.ball_mem_nhds _ ha'
        have h := (tendsto_def.1 hpot' _ hball')
        simpa [Metric.ball, Set.mem_setOf_eq, Real.dist_eq] using h
      have hesc : ∀ᶠ z in atInfinity, ‖z‖ > escape_bound c :=
        eventually_atInfinity_norm_gt (escape_bound c)
      have hboth := (hpot.and hesc)
      refine hboth.mono ?_
      intro z hz
      rcases hz with ⟨hpotz, hzesc⟩
      have hesc0 : ‖Quadratic.orbit c z 0‖ > escape_bound c := by
        simpa [Quadratic.orbit] using hzesc
      have hescN :
          ‖Quadratic.orbit c z N‖ > escape_bound c := by
        exact norm_orbit_gt_escape_bound_of_ge c z 0 N (Nat.zero_le _) hesc0
      have hdist :
          dist (Quadratic.potential_seq c z N) (Quadratic.green_function c z) ≤
            (2 ^ N : ℝ)⁻¹ * M := by
        simpa [M, one_div, inv_pow] using
          (dist_potential_seq_green_function_le_of_escaping c z N hescN)
      have h1 : 1 ≤ ‖(quadratic_map c)^[N] z‖ :=
        norm_iterate_ge_one_of_escape c z hzesc N
      have hpot_eq :
          Quadratic.potential_seq c z N =
            (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ := by
        exact potential_seq_eq_log_norm_iterate c z N h1
      have hpotz' :
          |Quadratic.potential_seq c z N - Real.log ‖z‖| < a / 2 := by
        simpa [hpot_eq] using hpotz
      have hpotz'' :
          |Quadratic.potential_seq c z N - Real.log ‖z‖| ≤ a / 2 := le_of_lt hpotz'
      have hdist' :
          |Quadratic.green_function c z - Quadratic.potential_seq c z N| ≤ (2 ^ N : ℝ)⁻¹ * M := by
        simpa [Real.dist_eq, abs_sub_comm] using hdist
      have htri :
          |Quadratic.green_function c z - Real.log ‖z‖| ≤
            |Quadratic.green_function c z - Quadratic.potential_seq c z N| +
              |Quadratic.potential_seq c z N - Real.log ‖z‖| :=
        abs_sub_le _ _ _
      have hle :
          |Quadratic.green_function c z - Real.log ‖z‖| ≤ (2 ^ N : ℝ)⁻¹ * M + a / 2 :=
        htri.trans (add_le_add hdist' hpotz'')
      have hlt : (2 ^ N : ℝ)⁻¹ * M + a / 2 < a := by
        have h := add_lt_add_right hNbound (a / 2)
        have h' : a / 2 + a / 2 = a := by
          ring
        simpa [h', add_comm, add_left_comm, add_assoc] using h
      exact lt_of_le_of_lt hle hlt
  simpa [Real.norm_eq_abs] using hgoal

lemma tendsto_norm_bottcher_map_div_norm_atInfinity (c : ℂ) :
    Tendsto (fun z => ‖Quadratic.bottcher_map c z‖ / ‖z‖) atInfinity (𝓝 (1 : ℝ)) := by
  have hgreen := tendsto_green_function_minus_log_norm_atInfinity c
  have hExp :
      Tendsto (fun z => Real.exp (Quadratic.green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (Real.exp (0 : ℝ))) :=
    (Real.continuous_exp.tendsto (0 : ℝ)).comp hgreen
  have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
    eventually_atInfinity_norm_gt (0 : ℝ)
  have hratio :
      (fun z => ‖Quadratic.bottcher_map c z‖ / ‖z‖) =ᶠ[atInfinity]
        fun z => Real.exp (Quadratic.green_function c z - Real.log ‖z‖) := by
    refine hpos.mono ?_
    intro z hz
    have hb : ‖Quadratic.bottcher_map c z‖ =
        Real.exp (Quadratic.green_function c z) :=
      Quadratic.norm_bottcher_eq_exp_green c z
    have hz' : Real.exp (Real.log ‖z‖) = ‖z‖ := by
      simpa using (Real.exp_log hz)
    calc
      ‖Quadratic.bottcher_map c z‖ / ‖z‖
          = Real.exp (Quadratic.green_function c z) / ‖z‖ := by
              simp [hb]
      _ = Real.exp (Quadratic.green_function c z) / Real.exp (Real.log ‖z‖) := by
              simp [hz']
      _ = Real.exp (Quadratic.green_function c z - Real.log ‖z‖) := by
              simp [Real.exp_sub]
  have hExp' : Tendsto (fun z => Real.exp (Quadratic.green_function c z - Real.log ‖z‖))
      atInfinity (𝓝 (1 : ℝ)) := by
    simpa using hExp
  exact (tendsto_congr' hratio).2 hExp'

lemma tendsto_bottcher_map_div_atInfinity (c : ℂ) :
    Tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 (1 : ℂ)) := by
  have hgreen := tendsto_green_function_minus_log_norm_atInfinity c
  have hExpR :
      Tendsto (fun z => Real.exp (Quadratic.green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (Real.exp (0 : ℝ))) :=
    (Real.continuous_exp.tendsto (0 : ℝ)).comp hgreen
  have hExpR' :
      Tendsto (fun z => Real.exp (Quadratic.green_function c z - Real.log ‖z‖))
        atInfinity (𝓝 (1 : ℝ)) := by
    simpa using hExpR
  have hExpC :
      Tendsto (fun z => ((Real.exp (Quadratic.green_function c z - Real.log ‖z‖)) : ℂ))
        atInfinity (𝓝 (1 : ℂ)) := by
    exact (Filter.tendsto_ofReal_iff).2 hExpR'
  have hpos : ∀ᶠ z in atInfinity, 0 < ‖z‖ :=
    eventually_atInfinity_norm_gt (0 : ℝ)
  have hratio :
      (fun z => (Quadratic.bottcher_map c z) / z) =ᶠ[atInfinity]
        fun z => ((Real.exp (Quadratic.green_function c z - Real.log ‖z‖)) : ℂ) := by
    refine hpos.mono ?_
    intro z hz
    have hz' : z ≠ 0 := by
      exact (norm_ne_zero_iff).1 (ne_of_gt hz)
    have hz'' : (‖z‖ : ℝ) ≠ 0 := by
      exact ne_of_gt hz
    have hz''' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hz''
    calc
      (Quadratic.bottcher_map c z) / z
          = ((z / ↑‖z‖) * (Real.exp (Quadratic.green_function c z)) : ℂ) / z := by
              simp [Quadratic.bottcher_map, hz']
      _ = ((Real.exp (Quadratic.green_function c z)) : ℂ) / (‖z‖ : ℂ) := by
              field_simp [hz', hz''', mul_comm, mul_left_comm, mul_assoc]
      _ = ((Real.exp (Quadratic.green_function c z - Real.log ‖z‖)) : ℂ) := by
              simp [Real.exp_sub, Real.exp_log hz, div_eq_mul_inv]
  exact (tendsto_congr' hratio).2 hExpC

lemma bottcher_normalized_at_infty_of_green (c : ℂ) : bottcher_normalized_at_infty c := by
  exact tendsto_bottcher_map_div_atInfinity c

lemma bottcher_normalized_at_infty_norm_proof (c : ℂ) :
    bottcher_normalized_at_infty_norm c := by
  exact tendsto_norm_bottcher_map_div_norm_atInfinity c

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

/-- Continuity of `bottcher_map` away from `0` (outside-plan namespace helper). -/
lemma bottcher_map_continuousAt_of_ne_zero_outsidePlan (c z : ℂ) (hz : z ≠ 0) :
    ContinuousAt (Quadratic.bottcher_map c) z := by
  have hnorm_ne : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hdiv : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
    continuousAt_id.div
      ((Complex.continuous_ofReal.comp continuous_norm).continuousAt) hnorm_ne
  have hif :
      (fun w : ℂ => if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) =ᶠ[𝓝 z]
        (fun w : ℂ => w / (‖w‖ : ℂ)) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [hw]
  have hdir : ContinuousAt (fun w : ℂ => if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) z :=
    hdiv.congr_of_eventuallyEq hif
  have hexp :
      ContinuousAt (fun w : ℂ => (Real.exp (MLC.Quadratic.green_function c w) : ℂ)) z :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (MLC.Quadratic.continuous_green_function c))).continuousAt
  change ContinuousAt
    (fun w : ℂ =>
      (if w = 0 then (1 : ℂ) else w / (‖w‖ : ℂ)) *
        (Real.exp (MLC.Quadratic.green_function c w) : ℂ)) z
  exact hdir.mul hexp

lemma bottcher_map_re_neg_of_pos_real (c : ℂ) {t : ℝ} (ht : 0 < t) :
    (Quadratic.bottcher_map c (-t)).re < 0 := by
  have ht0 : (-t : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast (ne_of_gt ht))
  rw [Quadratic.bottcher_map, if_neg ht0, Complex.mul_re]
  have hr : (((-t : ℂ) / ‖(-t : ℂ)‖).re) = -1 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, ht.ne']
  have hi : (((-t : ℂ) / ‖(-t : ℂ)‖).im) = 0 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, ht.ne']
  rw [hr, hi]
  simpa [Complex.exp_ofReal_re] using Real.exp_pos (MLC.Quadratic.green_function c (-t))

lemma bottcher_map_not_continuousAt_zero (c : ℂ) :
    ¬ ContinuousAt (Quadratic.bottcher_map c) 0 := by
  intro hcont
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hU_nhds : U ∈ 𝓝 (Quadratic.bottcher_map c 0) := by
    have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hmem : Quadratic.bottcher_map c 0 ∈ U := by
      simp [U, Quadratic.bottcher_map, Complex.exp_ofReal_re, Real.exp_pos]
    exact hUopen.mem_nhds hmem
  have hpre : (Quadratic.bottcher_map c) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds hU_nhds
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hεpos, hball⟩
  have hhalfpos : 0 < ε / 2 := by linarith
  let z : ℂ := (-(ε / 2) : ℝ)
  have hzdist : dist z 0 = ε / 2 := by
    simp [z, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hεpos]
  have hzball : z ∈ Metric.ball (0 : ℂ) ε := by
    have : dist z 0 < ε := by rw [hzdist]; linarith
    simpa [Metric.ball, Set.mem_setOf_eq] using this
  have hzU : Quadratic.bottcher_map c z ∈ U := hball hzball
  have hzneg : (Quadratic.bottcher_map c z).re < 0 := by
    simpa [z] using bottcher_map_re_neg_of_pos_real c hhalfpos
  exact (not_lt_of_ge (le_of_lt hzneg)) hzU

lemma bottcher_map_not_continuous (c : ℂ) :
    ¬ Continuous (Quadratic.bottcher_map c) := by
  intro hcont
  exact bottcher_map_not_continuousAt_zero c hcont.continuousAt

lemma bottcher_map_not_isProperMap (c : ℂ) :
    ¬ IsProperMap (Quadratic.bottcher_map c) := by
  intro hproper
  exact bottcher_map_not_continuous c hproper.continuous

lemma isDiscrete_fiber_of_isLocallyInjective
    {f : ℂ → ℂ} (hlocal : IsLocallyInjective f) (y : ℂ) :
    IsDiscrete {x : ℂ | f x = y} := by
  classical
  -- Use the characterization: each point has an open neighborhood
  -- whose intersection with the fiber is a singleton.
  refine (isDiscrete_iff_forall_exists_isOpen).2 ?_
  intro x hx
  rcases hlocal x with ⟨U, hUopen, hxU, hUinj⟩
  refine ⟨U, hUopen, ?_⟩
  ext z
  constructor
  · intro hz
    have hzU : z ∈ U := hz.1
    have hzf : f z = y := hz.2
    have hxf : f x = y := hx
    have : z = x := hUinj hzU hxU (by simp [hxf, hzf])
    simp [this]
  · intro hz
    rcases hz with rfl
    exact ⟨hxU, hx⟩

lemma finite_fiber_of_isProperMap_isLocallyInjective
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hlocal : IsLocallyInjective f) (y : ℂ) :
    ({x : ℂ | f x = y} : Set ℂ).Finite := by
  have hcompact : IsCompact ((fun x : ℂ => f x) ⁻¹' {y}) :=
    hproper.isCompact_preimage isCompact_singleton
  have hdisc : IsDiscrete ({x : ℂ | f x = y} : Set ℂ) :=
    isDiscrete_fiber_of_isLocallyInjective hlocal y
  -- Convert preimage of singleton into the fiber set.
  have hpre : (f ⁻¹' ({y} : Set ℂ)) = ({x : ℂ | f x = y} : Set ℂ) := by
    ext x
    simp
  simpa [hpre] using hcompact.finite hdisc

lemma isDiscrete_fiber_of_isLocalHomeomorphOn_of_fiber_subset
    {f : ℂ → ℂ} {s : Set ℂ} (hlocal : IsLocalHomeomorphOn f s) {y : ℂ}
    (hfiber : ({x : ℂ | f x = y} : Set ℂ) ⊆ s) :
    IsDiscrete ({x : ℂ | f x = y} : Set ℂ) := by
  classical
  refine (isDiscrete_iff_forall_exists_isOpen).2 ?_
  intro x hx
  have hxS : x ∈ s := hfiber hx
  rcases hlocal x hxS with ⟨e, hx_source, hfeq⟩
  refine ⟨e.source, e.open_source, ?_⟩
  ext z
  constructor
  · intro hz
    have hz_source : z ∈ e.source := hz.1
    have hzf : f z = y := hz.2
    have hxf : f x = y := hx
    have hEq : f z = f x := by simp [hzf, hxf]
    have hzEq : z = x := by
      have heq : e z = e x := by simpa [hfeq] using hEq
      exact e.toPartialEquiv.injOn hz_source hx_source heq
    simp [hzEq]
  · intro hz
    rcases hz with rfl
    exact ⟨hx_source, hx⟩

lemma finite_fiber_of_isProperMap_isLocalHomeomorphOn_of_fiber_subset
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    {y : ℂ} (hfiber : ({x : ℂ | f x = y} : Set ℂ) ⊆ s) :
    ({x : ℂ | f x = y} : Set ℂ).Finite := by
  have hcompact : IsCompact ((fun x : ℂ => f x) ⁻¹' {y}) :=
    hproper.isCompact_preimage isCompact_singleton
  have hdisc : IsDiscrete ({x : ℂ | f x = y} : Set ℂ) :=
    isDiscrete_fiber_of_isLocalHomeomorphOn_of_fiber_subset hlocal hfiber
  have hpre : (f ⁻¹' ({y} : Set ℂ)) = ({x : ℂ | f x = y} : Set ℂ) := by
    ext x
    simp
  simpa [hpre] using hcompact.finite hdisc

lemma finite_of_isCompact_isDiscrete {s : Set ℂ} (hs : IsCompact s) (hs' : IsDiscrete s) :
    s.Finite :=
  hs.finite hs'

lemma range_isOpen_of_isLocalHomeomorph {f : ℂ → ℂ} (hlocal : IsLocalHomeomorph f) :
    IsOpen (Set.range f) := by
  have hOpenMap : IsOpenMap f := hlocal.isOpenMap
  simpa [Set.image_univ] using (hOpenMap Set.univ isOpen_univ)

lemma range_isClosed_of_isProperMap {f : ℂ → ℂ} (hproper : IsProperMap f) :
    IsClosed (Set.range f) := by
  have hClosedMap : IsClosedMap f := hproper.isClosedMap
  simpa [Set.image_univ] using (hClosedMap Set.univ isClosed_univ)

lemma range_eq_univ_of_isProperMap_isLocalHomeomorph
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f)
    (hnonempty : (Set.range f).Nonempty) :
    Set.range f = Set.univ := by
  have hopen : IsOpen (Set.range f) := range_isOpen_of_isLocalHomeomorph hlocal
  have hclosed : IsClosed (Set.range f) := range_isClosed_of_isProperMap hproper
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  simpa using (IsClopen.eq_univ (α := ℂ) hclopen hnonempty)

lemma exists_open_preimage_subset_of_closedMap_of_fiber_subset
    {f : ℂ → ℂ} (hclosed : IsClosedMap f) {y : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hfiber : ({x : ℂ | f x = y} : Set ℂ) ⊆ U) :
    ∃ V, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  have hy_not_in : y ∉ f '' Uᶜ := by
    intro hy
    rcases hy with ⟨x, hxU, hxy⟩
    have hxFiber : x ∈ ({x : ℂ | f x = y} : Set ℂ) := by
      simp [Set.mem_setOf_eq, hxy]
    exact hxU (hfiber hxFiber)
  let V : Set ℂ := (f '' Uᶜ)ᶜ
  have hVopen : IsOpen V := by
    change IsOpen ((f '' Uᶜ)ᶜ)
    exact (hclosed _ hUopen.isClosed_compl).isOpen_compl
  have hyV : y ∈ V := by
    simpa [V] using hy_not_in
  refine ⟨V, hVopen, hyV, ?_⟩
  intro x hx
  by_contra hxU
  have : f x ∈ f '' Uᶜ := ⟨x, hxU, rfl⟩
  exact hx this

lemma exists_open_preimage_subset_union_of_finite_fiber
    {f : ℂ → ℂ} (hlocal : IsLocalHomeomorph f) (hclosed : IsClosedMap f)
    {y : ℂ} (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∃ U : Set ℂ, f ⁻¹' V ⊆ U := by
  classical
  -- Choose local homeomorphs around each point in the fiber.
  let F : Finset ℂ := hfinite.toFinset
  have hF : (F : Set ℂ) = {x : ℂ | f x = y} := by
    exact Finite.coe_toFinset hfinite
  let e : ℂ → OpenPartialHomeomorph ℂ ℂ := fun x => Classical.choose (hlocal x)
  have hx_source : ∀ x : ℂ, x ∈ (e x).source := fun x => (Classical.choose_spec (hlocal x)).1
  have hfeq : ∀ x : ℂ, f = (e x) := fun x => (Classical.choose_spec (hlocal x)).2
  let U : Set ℂ := ⋃ x ∈ F, (e x).source
  let V0 : Set ℂ := ⋂ x ∈ F, (e x).target
  have hUmem : {x : ℂ | f x = y} ⊆ U := by
    intro x hx
    have hxF : x ∈ F := by
      have : x ∈ (F : Set ℂ) := by simpa [hF] using hx
      simpa using this
    exact mem_iUnion₂.mpr ⟨x, hxF, hx_source x⟩
  have hyV0 : y ∈ V0 := by
    -- `y` lies in every target, since `f x = y` and `f = e x`.
    classical
    simp [V0]
    intro x hxF
    have hx : f x = y := by
      have : x ∈ (F : Set ℂ) := by simpa using hxF
      simpa [hF] using this
    have hxsource : x ∈ (e x).source := hx_source x
    have hmap : (e x) x ∈ (e x).target := (e x).source_preimage_target hxsource
    have hfa : f = (e x) := hfeq x
    have hyx : (e x) x = y := by simpa [hfa] using hx
    exact hyx ▸ hmap
  have hV0open : IsOpen V0 := by
    classical
    unfold V0
    refine isOpen_biInter_finset ?_
    intro x hx
    exact (e x).open_target
  have hy_not_in : y ∉ f '' Uᶜ := by
    intro hy
    rcases hy with ⟨x, hxU, rfl⟩
    exact hxU (hUmem rfl)
  have hUopen : IsOpen U := by
    unfold U
    refine isOpen_iUnion ?_
    intro x
    refine isOpen_iUnion ?_
    intro hx
    exact (e x).open_source
  have hclosedU : IsClosed (f '' Uᶜ) := hclosed _ ((isClosed_compl_iff).2 hUopen)
  let V : Set ℂ := V0 \ f '' Uᶜ
  have hVopen : IsOpen V := IsOpen.sdiff hV0open hclosedU
  have hyV : y ∈ V := by
    exact ⟨hyV0, hy_not_in⟩
  refine ⟨V, hVopen, hyV, U, ?_⟩
  intro x hx
  have hxV : f x ∈ V := hx
  have hnot : f x ∉ f '' Uᶜ := hxV.2
  by_contra hxU
  exact hnot ⟨x, hxU, rfl⟩

lemma exists_pairwise_disjoint_ball_of_finite {s : Set ℂ} (hs : s.Finite) :
    ∃ r : s → ℝ, (∀ x, 0 < r x) ∧
      Pairwise (fun x y => Disjoint (Metric.ball x.1 (r x)) (Metric.ball y.1 (r y))) := by
  classical
  by_cases hsubs : s.Subsingleton
  · refine ⟨fun _ => (1 : ℝ), ?_, ?_⟩
    · intro x; norm_num
    · intro x y hne
      have : x = y := by
        have hxy : x.1 = y.1 := hsubs x.property y.property
        exact Subtype.ext hxy
      exact (hne this).elim
  · -- Define radii using `infDist` to the rest of the finite set.
    let r : s → ℝ := fun x =>
      if hne : (s \ {x.1}).Nonempty then
        (Metric.infDist x.1 (s \ {x.1})) / 2
      else 1
    have hrpos : ∀ x, 0 < r x := by
      intro x
      by_cases hne : (s \ {x.1}).Nonempty
      · have hclosed : IsClosed (s \ {x.1}) :=
          (hs.subset (by intro y hy; exact hy.1)).isClosed
        have hxnot : x.1 ∉ s \ {x.1} := by
          simp
        have hpos : 0 < Metric.infDist x.1 (s \ {x.1}) := by
          have := (IsClosed.notMem_iff_infDist_pos (x := x.1) (s := s \ {x.1}) hclosed hne).1
          exact this hxnot
        have hpos' : 0 < Metric.infDist x.1 (s \ {x.1}) / 2 := by
          nlinarith
        simpa [r, hne] using hpos'
      · simp [r, hne]
    refine ⟨r, hrpos, ?_⟩
    intro x y hne
    have hxy : x.1 ≠ y.1 := by
      intro h
      apply hne
      exact Subtype.ext h
    have hy_mem : y.1 ∈ s \ {x.1} := by
      exact ⟨y.property, by simpa [Set.mem_singleton_iff, eq_comm] using hxy⟩
    have hx_mem : x.1 ∈ s \ {y.1} := by
      exact ⟨x.property, by simpa [Set.mem_singleton_iff] using hxy⟩
    have hxne : (s \ {x.1}).Nonempty := ⟨y.1, hy_mem⟩
    have hyne : (s \ {y.1}).Nonempty := ⟨x.1, hx_mem⟩
    have hxle : r x ≤ dist x.1 y.1 / 2 := by
      have h := Metric.infDist_le_dist_of_mem (x := x.1) (s := s \ {x.1}) hy_mem
      have h' : Metric.infDist x.1 (s \ {x.1}) / 2 ≤ dist x.1 y.1 / 2 := by
        nlinarith [h]
      simpa [r, hxne] using h'
    have hyle : r y ≤ dist x.1 y.1 / 2 := by
      have h := Metric.infDist_le_dist_of_mem (x := y.1) (s := s \ {y.1}) hx_mem
      have h' : Metric.infDist y.1 (s \ {y.1}) / 2 ≤ dist y.1 x.1 / 2 := by
        nlinarith [h]
      have h'' : dist y.1 x.1 = dist x.1 y.1 := by simp [dist_comm]
      simpa [r, hyne, h''] using h'
    have hsum : r x + r y ≤ dist x.1 y.1 := by
      have : r x + r y ≤ dist x.1 y.1 / 2 + dist x.1 y.1 / 2 :=
        add_le_add hxle hyle
      have hhalf : dist x.1 y.1 / 2 + dist x.1 y.1 / 2 = dist x.1 y.1 := by ring
      simpa [hhalf] using this
    exact Metric.ball_disjoint_ball hsum

lemma exists_open_preimage_subset_iUnion_ball_of_finite_fiber
    {f : ℂ → ℂ} (hclosed : IsClosedMap f) {y : ℂ}
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∃ r : ({x : ℂ // f x = y}) → ℝ,
        (∀ x, 0 < r x) ∧
        Pairwise (fun x x' =>
          Disjoint (Metric.ball x.1 (r x)) (Metric.ball x'.1 (r x'))) ∧
        f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), Metric.ball x.1 (r x) := by
  let s : Set ℂ := {x : ℂ | f x = y}
  have hsfinite : s.Finite := by simpa [s] using hfinite
  rcases exists_pairwise_disjoint_ball_of_finite (s := s) hsfinite with ⟨r, hrpos, hrdisj⟩
  let U : Set ℂ := ⋃ x : ({x : ℂ // f x = y}), Metric.ball x.1 (r x)
  have hUopen : IsOpen U := by
    unfold U
    exact isOpen_iUnion (fun x => Metric.isOpen_ball)
  have hsU : s ⊆ U := by
    intro x hx
    refine mem_iUnion.2 ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (hrpos ⟨x, hx⟩)
  rcases exists_open_preimage_subset_of_closedMap_of_fiber_subset
    (f := f) hclosed (y := y) (U := U) hUopen hsU with ⟨V, hVopen, hyV, hpre⟩
  refine ⟨V, hVopen, hyV, r, hrpos, hrdisj, ?_⟩
  simpa [U] using hpre

lemma exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber
    {f : ℂ → ℂ} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorph f) {y : ℂ}
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∃ U : ({x : ℂ // f x = y}) → Set ℂ,
        (∀ x, IsOpen (U x)) ∧
        (∀ x, x.1 ∈ U x) ∧
        (∀ x, Set.InjOn f (U x)) ∧
        Pairwise (fun x x' => Disjoint (U x) (U x')) ∧
        f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x := by
  classical
  have hlocinj : IsLocallyInjective f := hlocal.isLocallyInjective
  choose N hNopen hxN hNinj using (fun x : ({x : ℂ // f x = y}) => hlocinj x.1)
  let s : Set ℂ := {x : ℂ | f x = y}
  have hsfinite : s.Finite := by simpa [s] using hfinite
  rcases exists_pairwise_disjoint_ball_of_finite (s := s) hsfinite with ⟨r, hrpos, hrdisj⟩
  let U : ({x : ℂ // f x = y}) → Set ℂ := fun x => Metric.ball x.1 (r x) ∩ N x
  let Uunion : Set ℂ := ⋃ x : ({x : ℂ // f x = y}), U x
  have hUopen : IsOpen Uunion := by
    unfold Uunion
    refine isOpen_iUnion ?_
    intro x
    exact (Metric.isOpen_ball.inter (hNopen x))
  have hsU : s ⊆ Uunion := by
    intro x hx
    refine mem_iUnion.2 ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    exact ⟨Metric.mem_ball_self (hrpos ⟨x, hx⟩), hxN ⟨x, hx⟩⟩
  rcases exists_open_preimage_subset_of_closedMap_of_fiber_subset
    (f := f) hclosed (y := y) (U := Uunion) hUopen hsU with ⟨V, hVopen, hyV, hpre⟩
  refine ⟨V, hVopen, hyV, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (Metric.isOpen_ball.inter (hNopen x))
  · intro x
    exact ⟨Metric.mem_ball_self (hrpos x), hxN x⟩
  · intro x
    exact (hNinj x).mono (by intro z hz; exact hz.2)
  · intro x x' hxx'
    exact (hrdisj hxx').mono (by intro z hz; exact hz.1) (by intro z hz; exact hz.1)
  · simpa [Uunion] using hpre

lemma exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber_on
    {f : ℂ → ℂ} {s : Set ℂ} (hclosed : IsClosedMap f)
    (hlocal : IsLocalHomeomorphOn f s) {y : ℂ}
    (hfiberS : ({x : ℂ | f x = y} : Set ℂ) ⊆ s)
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∃ U : ({x : ℂ // f x = y}) → Set ℂ,
        (∀ x, IsOpen (U x)) ∧
        (∀ x, x.1 ∈ U x) ∧
        (∀ x, Set.InjOn f (U x)) ∧
        Pairwise (fun x x' => Disjoint (U x) (U x')) ∧
        f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x := by
  classical
  let s0 : Set ℂ := {x : ℂ | f x = y}
  have hsfinite : s0.Finite := by simpa [s0] using hfinite
  rcases exists_pairwise_disjoint_ball_of_finite (s := s0) hsfinite with ⟨r, hrpos, hrdisj⟩
  let N : ({x : ℂ // f x = y}) → Set ℂ := fun x =>
    (Classical.choose (hlocal x.1 (hfiberS x.2))).source
  have hNopen : ∀ x, IsOpen (N x) := by
    intro x
    exact (Classical.choose (hlocal x.1 (hfiberS x.2))).open_source
  have hxN : ∀ x, x.1 ∈ N x := by
    intro x
    exact (Classical.choose_spec (hlocal x.1 (hfiberS x.2))).1
  have hNinj : ∀ x, Set.InjOn f (N x) := by
    intro x a ha b hb hab
    let e : OpenPartialHomeomorph ℂ ℂ := Classical.choose (hlocal x.1 (hfiberS x.2))
    have hfeq : f = e := (Classical.choose_spec (hlocal x.1 (hfiberS x.2))).2
    have heq : e a = e b := by simpa [hfeq] using hab
    exact e.toPartialEquiv.injOn (by simpa [N, e] using ha) (by simpa [N, e] using hb) heq
  let U : ({x : ℂ // f x = y}) → Set ℂ := fun x => Metric.ball x.1 (r x) ∩ N x
  let Uunion : Set ℂ := ⋃ x : ({x : ℂ // f x = y}), U x
  have hUopen : IsOpen Uunion := by
    unfold Uunion
    refine isOpen_iUnion ?_
    intro x
    exact (Metric.isOpen_ball.inter (hNopen x))
  have hsU : s0 ⊆ Uunion := by
    intro x hx
    refine mem_iUnion.2 ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    exact ⟨Metric.mem_ball_self (hrpos ⟨x, hx⟩), hxN ⟨x, hx⟩⟩
  rcases exists_open_preimage_subset_of_closedMap_of_fiber_subset
    (f := f) hclosed (y := y) (U := Uunion) hUopen hsU with ⟨V, hVopen, hyV, hpre⟩
  refine ⟨V, hVopen, hyV, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (Metric.isOpen_ball.inter (hNopen x))
  · intro x
    exact ⟨Metric.mem_ball_self (hrpos x), hxN x⟩
  · intro x
    exact (hNinj x).mono (by intro z hz; exact hz.2)
  · intro x x' hxx'
    exact (hrdisj hxx').mono (by intro z hz; exact hz.1) (by intro z hz; exact hz.1)
  · simpa [Uunion] using hpre

lemma exists_open_preimage_subset_iUnion_disjoint_inj_subset_of_finite_fiber_on
    {f : ℂ → ℂ} {s : Set ℂ} (hclosed : IsClosedMap f)
    (hlocal : IsLocalHomeomorphOn f s) (hsopen : IsOpen s) {y : ℂ}
    (hfiberS : ({x : ℂ | f x = y} : Set ℂ) ⊆ s)
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∃ U : ({x : ℂ // f x = y}) → Set ℂ,
        (∀ x, IsOpen (U x)) ∧
        (∀ x, x.1 ∈ U x) ∧
        (∀ x, U x ⊆ s) ∧
        (∀ x, Set.InjOn f (U x)) ∧
        Pairwise (fun x x' => Disjoint (U x) (U x')) ∧
        f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x := by
  classical
  let s0 : Set ℂ := {x : ℂ | f x = y}
  have hsfinite : s0.Finite := by simpa [s0] using hfinite
  rcases exists_pairwise_disjoint_ball_of_finite (s := s0) hsfinite with ⟨r, hrpos, hrdisj⟩
  let N : ({x : ℂ // f x = y}) → Set ℂ := fun x =>
    (Classical.choose (hlocal x.1 (hfiberS x.2))).source
  have hNopen : ∀ x, IsOpen (N x) := by
    intro x
    exact (Classical.choose (hlocal x.1 (hfiberS x.2))).open_source
  have hxN : ∀ x, x.1 ∈ N x := by
    intro x
    exact (Classical.choose_spec (hlocal x.1 (hfiberS x.2))).1
  have hNinj : ∀ x, Set.InjOn f (N x) := by
    intro x a ha b hb hab
    let e : OpenPartialHomeomorph ℂ ℂ := Classical.choose (hlocal x.1 (hfiberS x.2))
    have hfeq : f = e := (Classical.choose_spec (hlocal x.1 (hfiberS x.2))).2
    have heq : e a = e b := by simpa [hfeq] using hab
    exact e.toPartialEquiv.injOn (by simpa [N, e] using ha) (by simpa [N, e] using hb) heq
  let U : ({x : ℂ // f x = y}) → Set ℂ := fun x => Metric.ball x.1 (r x) ∩ N x ∩ s
  let Uunion : Set ℂ := ⋃ x : ({x : ℂ // f x = y}), U x
  have hUopen : IsOpen Uunion := by
    unfold Uunion
    refine isOpen_iUnion ?_
    intro x
    exact (Metric.isOpen_ball.inter (hNopen x)).inter hsopen
  have hsU : s0 ⊆ Uunion := by
    intro x hx
    refine mem_iUnion.2 ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    exact ⟨⟨Metric.mem_ball_self (hrpos ⟨x, hx⟩), hxN ⟨x, hx⟩⟩, hfiberS hx⟩
  rcases exists_open_preimage_subset_of_closedMap_of_fiber_subset
    (f := f) hclosed (y := y) (U := Uunion) hUopen hsU with ⟨V, hVopen, hyV, hpre⟩
  refine ⟨V, hVopen, hyV, U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (Metric.isOpen_ball.inter (hNopen x)).inter hsopen
  · intro x
    exact ⟨⟨Metric.mem_ball_self (hrpos x), hxN x⟩, hfiberS x.2⟩
  · intro x z hz
    exact hz.2
  · intro x
    exact (hNinj x).mono (by intro z hz; exact hz.1.2)
  · intro x x' hxx'
    exact (hrdisj hxx').mono (by intro z hz; exact hz.1.1) (by intro z hz; exact hz.1.1)
  · simpa [Uunion] using hpre

lemma exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj
    {f : ℂ → ℂ} {y : ℂ} {V : Set ℂ}
    {U : ({x : ℂ // f x = y}) → Set ℂ}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    {y' : ℂ} (hy' : y' ∈ V) :
    ∃ g : ({x : ℂ // f x = y'}) → ({x : ℂ // f x = y}),
      Function.Injective g := by
  classical
  let g : ({x : ℂ // f x = y'}) → ({x : ℂ // f x = y}) := fun z =>
    Classical.choose <| by
      have hzpre : z.1 ∈ f ⁻¹' V := by
        simpa [Set.preimage, z.2] using hy'
      have hzU : z.1 ∈ ⋃ x : ({x : ℂ // f x = y}), U x := hpre hzpre
      exact Set.mem_iUnion.mp hzU
  have hgmem : ∀ z : ({x : ℂ // f x = y'}), z.1 ∈ U (g z) := by
    intro z
    exact Classical.choose_spec <| by
      have hzpre : z.1 ∈ f ⁻¹' V := by
        simpa [Set.preimage, z.2] using hy'
      have hzU : z.1 ∈ ⋃ x : ({x : ℂ // f x = y}), U x := hpre hzpre
      exact Set.mem_iUnion.mp hzU
  refine ⟨g, ?_⟩
  intro z₁ z₂ hz
  have hz₁U : z₁.1 ∈ U (g z₁) := hgmem z₁
  have hz₂U : z₂.1 ∈ U (g z₁) := by
    simpa [hz] using hgmem z₂
  have hf : f z₁.1 = f z₂.1 := by
    simp [z₁.2, z₂.2]
  have hz₁₂ : z₁.1 = z₂.1 := (hUinj (g z₁)) hz₁U hz₂U hf
  exact Subtype.ext hz₁₂

lemma finite_fiber_of_mem_open_of_preimage_subset_iUnion_inj
    {f : ℂ → ℂ} {y : ℂ} {V : Set ℂ}
    {U : ({x : ℂ // f x = y}) → Set ℂ}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite)
    {y' : ℂ} (hy' : y' ∈ V) :
    ({x : ℂ | f x = y'} : Set ℂ).Finite := by
  classical
  rcases exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hy' with ⟨g, hg⟩
  haveI : Finite ({x : ℂ // f x = y}) := hfinite.to_subtype
  haveI : Finite ({x : ℂ // f x = y'}) := Finite.of_injective g hg
  exact (Set.finite_def).2 ⟨Fintype.ofFinite ({x : ℂ // f x = y'})⟩

lemma natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj
    {f : ℂ → ℂ} {y : ℂ} {V : Set ℂ}
    {U : ({x : ℂ // f x = y}) → Set ℂ}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite)
    {y' : ℂ} (hy' : y' ∈ V) :
    Nat.card ({x : ℂ // f x = y'}) ≤ Nat.card ({x : ℂ // f x = y}) := by
  classical
  rcases exists_injective_fiber_map_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hy' with ⟨g, hg⟩
  haveI : Finite ({x : ℂ // f x = y}) := hfinite.to_subtype
  haveI : Finite ({x : ℂ // f x = y'}) := Finite.of_injective g hg
  exact Nat.card_le_card_of_injective g hg

lemma exists_open_finite_fiber_of_closedMap_localHomeomorph_of_finite_fiber
    {f : ℂ → ℂ} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorph f) {y : ℂ}
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∀ y' ∈ V, ({x : ℂ | f x = y'} : Set ℂ).Finite := by
  rcases exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber
      (f := f) hclosed hlocal (y := y) hfinite with
    ⟨V, hVopen, hyV, U, _hUopen, _hxU, hUinj, _hUdisj, hpre⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  exact finite_fiber_of_mem_open_of_preimage_subset_iUnion_inj
    (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hy'

lemma exists_open_natCard_fiber_le_of_closedMap_localHomeomorph_of_finite_fiber
    {f : ℂ → ℂ} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorph f) {y : ℂ}
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∀ y' ∈ V, Nat.card ({x : ℂ // f x = y'}) ≤ Nat.card ({x : ℂ // f x = y}) := by
  rcases exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber
      (f := f) hclosed hlocal (y := y) hfinite with
    ⟨V, hVopen, hyV, U, _hUopen, _hxU, hUinj, _hUdisj, hpre⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  exact natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj
    (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hy'

lemma exists_open_natCard_fiber_le_of_closedMap_localHomeomorphOn_of_finite_fiber_subset
    {f : ℂ → ℂ} {s : Set ℂ} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorphOn f s) {y : ℂ}
    (hfiberS : ({x : ℂ | f x = y} : Set ℂ) ⊆ s)
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∀ y' ∈ V, Nat.card ({x : ℂ // f x = y'}) ≤ Nat.card ({x : ℂ // f x = y}) := by
  rcases exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber_on
      (f := f) (s := s) hclosed hlocal (y := y) hfiberS hfinite with
    ⟨V, hVopen, hyV, U, _hUopen, _hxU, hUinj, _hUdisj, hpre⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  exact natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj
    (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hy'

lemma isOpen_image_of_isLocalHomeomorphOn_aux
    {f : ℂ → ℂ} {s t : Set ℂ} (hlocal : IsLocalHomeomorphOn f s)
    (ht : t ⊆ s) (htop : IsOpen t) :
    IsOpen (f '' t) := by
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

lemma exists_injective_fiber_map_of_mem_iInter_image_of_pairwise_disjoint
    {f : ℂ → ℂ} {y : ℂ}
    {U : ({x : ℂ // f x = y}) → Set ℂ}
    (hUdisj : Pairwise (fun x x' => Disjoint (U x) (U x')))
    {y' : ℂ} (hy' : y' ∈ ⋂ x : ({x : ℂ // f x = y}), f '' U x) :
    ∃ g : ({x : ℂ // f x = y}) → ({x : ℂ // f x = y'}),
      Function.Injective g := by
  classical
  let g : ({x : ℂ // f x = y}) → ({x : ℂ // f x = y'}) := fun x =>
    let hximg : y' ∈ f '' U x := Set.mem_iInter.mp hy' x
    ⟨Classical.choose hximg, (Classical.choose_spec hximg).2⟩
  have hgmem : ∀ x : ({x : ℂ // f x = y}), (g x).1 ∈ U x := by
    intro x
    dsimp [g]
    exact (Classical.choose_spec (Set.mem_iInter.mp hy' x)).1
  refine ⟨g, ?_⟩
  intro x₁ x₂ hx
  by_contra hne
  have hx₁U : (g x₁).1 ∈ U x₁ := hgmem x₁
  have hx₂U : (g x₂).1 ∈ U x₂ := hgmem x₂
  have hx₁U' : (g x₁).1 ∈ U x₂ := by
    simpa [hx] using hx₂U
  have hdisj : Disjoint (U x₁) (U x₂) := hUdisj hne
  exact (Set.disjoint_left.mp hdisj) hx₁U hx₁U'

lemma natCard_fiber_eq_of_mem_open_of_preimage_subset_iUnion_disjoint_inj_and_mem_iInter_image
    {f : ℂ → ℂ} {y : ℂ} {V : Set ℂ}
    {U : ({x : ℂ // f x = y}) → Set ℂ}
    (hpre : f ⁻¹' V ⊆ ⋃ x : ({x : ℂ // f x = y}), U x)
    (hUinj : ∀ x, Set.InjOn f (U x))
    (hUdisj : Pairwise (fun x x' => Disjoint (U x) (U x')))
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite)
    {y' : ℂ} (hyV : y' ∈ V)
    (hyI : y' ∈ ⋂ x : ({x : ℂ // f x = y}), f '' U x) :
    Nat.card ({x : ℂ // f x = y'}) = Nat.card ({x : ℂ // f x = y}) := by
  classical
  have hle :
      Nat.card ({x : ℂ // f x = y'}) ≤ Nat.card ({x : ℂ // f x = y}) :=
    natCard_fiber_le_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hyV
  have hfinite' : ({x : ℂ | f x = y'} : Set ℂ).Finite :=
    finite_fiber_of_mem_open_of_preimage_subset_iUnion_inj
      (f := f) (y := y) (V := V) (U := U) hpre hUinj hfinite hyV
  rcases exists_injective_fiber_map_of_mem_iInter_image_of_pairwise_disjoint
      (f := f) (y := y) (U := U) hUdisj hyI with ⟨g, hg⟩
  haveI : Finite ({x : ℂ // f x = y}) := hfinite.to_subtype
  haveI : Finite ({x : ℂ // f x = y'}) := hfinite'.to_subtype
  have hge :
      Nat.card ({x : ℂ // f x = y}) ≤ Nat.card ({x : ℂ // f x = y'}) :=
    Nat.card_le_card_of_injective g hg
  exact le_antisymm hle hge

lemma exists_open_natCard_fiber_eq_of_closedMap_localHomeomorph_of_finite_fiber
    {f : ℂ → ℂ} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorph f) {y : ℂ}
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∀ y' ∈ V, Nat.card ({x : ℂ // f x = y'}) = Nat.card ({x : ℂ // f x = y}) := by
  classical
  rcases exists_open_preimage_subset_iUnion_disjoint_inj_of_finite_fiber
      (f := f) hclosed hlocal (y := y) hfinite with
    ⟨V0, hV0open, hyV0, U, hUopen, hxU, hUinj, hUdisj, hpre⟩
  let I : Type := ({x : ℂ // f x = y})
  haveI : Finite I := hfinite.to_subtype
  letI : Fintype I := Fintype.ofFinite I
  have hOpenMap : IsOpenMap f := hlocal.isOpenMap
  let Iimgs : Set ℂ := ⋂ x : I, f '' U x
  have hIimgsOpen : IsOpen Iimgs := by
    unfold Iimgs
    simpa using
      (isOpen_biInter_finset (s := (Finset.univ : Finset I))
        (f := fun x : I => f '' U x) (by intro x _; exact hOpenMap _ (hUopen x)))
  let V : Set ℂ := V0 ∩ Iimgs
  have hVopen : IsOpen V := hV0open.inter hIimgsOpen
  have hyIimgs : y ∈ Iimgs := by
    refine Set.mem_iInter.mpr ?_
    intro x
    exact ⟨x.1, hxU x, by simp [x.2]⟩
  have hyV : y ∈ V := ⟨hyV0, hyIimgs⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  have hyV0' : y' ∈ V0 := hy'.1
  have hyI' : y' ∈ Iimgs := hy'.2
  exact natCard_fiber_eq_of_mem_open_of_preimage_subset_iUnion_disjoint_inj_and_mem_iInter_image
    (f := f) (y := y) (V := V0) (U := U) hpre hUinj hUdisj hfinite hyV0' hyI'

lemma exists_open_natCard_fiber_eq_of_closedMap_localHomeomorphOn_of_open_of_finite_fiber_subset
    {f : ℂ → ℂ} {s : Set ℂ} (hclosed : IsClosedMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s) {y : ℂ}
    (hfiberS : ({x : ℂ | f x = y} : Set ℂ) ⊆ s)
    (hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite) :
    ∃ V, IsOpen V ∧ y ∈ V ∧
      ∀ y' ∈ V, Nat.card ({x : ℂ // f x = y'}) = Nat.card ({x : ℂ // f x = y}) := by
  classical
  rcases exists_open_preimage_subset_iUnion_disjoint_inj_subset_of_finite_fiber_on
      (f := f) (s := s) hclosed hlocal hsopen (y := y) hfiberS hfinite with
    ⟨V0, hV0open, hyV0, U, hUopen, hxU, hUsub, hUinj, hUdisj, hpre⟩
  let I : Type := ({x : ℂ // f x = y})
  haveI : Finite I := hfinite.to_subtype
  letI : Fintype I := Fintype.ofFinite I
  let Iimgs : Set ℂ := ⋂ x : I, f '' U x
  have hIimgsOpen : IsOpen Iimgs := by
    unfold Iimgs
    simpa using
      (isOpen_biInter_finset (s := (Finset.univ : Finset I))
        (f := fun x : I => f '' U x) (by
          intro x _hx
          exact isOpen_image_of_isLocalHomeomorphOn_aux hlocal (hUsub x) (hUopen x)))
  let V : Set ℂ := V0 ∩ Iimgs
  have hVopen : IsOpen V := hV0open.inter hIimgsOpen
  have hyIimgs : y ∈ Iimgs := by
    refine Set.mem_iInter.mpr ?_
    intro x
    exact ⟨x.1, hxU x, by simp [x.2]⟩
  have hyV : y ∈ V := ⟨hyV0, hyIimgs⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  have hyV0' : y' ∈ V0 := hy'.1
  have hyI' : y' ∈ Iimgs := hy'.2
  exact natCard_fiber_eq_of_mem_open_of_preimage_subset_iUnion_disjoint_inj_and_mem_iInter_image
    (f := f) (y := y) (V := V0) (U := U) hpre hUinj hUdisj hfinite hyV0' hyI'

lemma natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorph
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) :
    IsLocallyConstant (fun y : ℂ => Nat.card ({x : ℂ // f x = y})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro y
  have hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite :=
    finite_fiber_of_isProperMap_isLocallyInjective
      (f := f) hproper hlocal.isLocallyInjective y
  rcases exists_open_natCard_fiber_eq_of_closedMap_localHomeomorph_of_finite_fiber
      (f := f) hproper.isClosedMap hlocal (y := y) hfinite with
    ⟨V, hVopen, hyV, hcard⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  exact hcard y' hy'

lemma natCard_fiber_eq_of_isProperMap_isLocalHomeomorph
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) :
    ∀ y y', Nat.card ({x : ℂ // f x = y}) = Nat.card ({x : ℂ // f x = y'}) := by
  have hloc :
      IsLocallyConstant (fun y : ℂ => Nat.card ({x : ℂ // f x = y})) :=
    natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorph
      (f := f) hproper hlocal
  exact (IsLocallyConstant.iff_is_const (f := fun y : ℂ =>
    Nat.card ({x : ℂ // f x = y}))).1 hloc

lemma injective_of_isProperMap_isLocalHomeomorph_of_exists_natCard_fiber_eq_one
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f)
    (hdeg1 : ∃ y : ℂ, Nat.card ({x : ℂ // f x = y}) = 1) :
    Function.Injective f := by
  rcases hdeg1 with ⟨y0, hy0⟩
  have hcard_const := natCard_fiber_eq_of_isProperMap_isLocalHomeomorph
    (f := f) hproper hlocal
  intro z w hzw
  have hcard : Nat.card ({x : ℂ // f x = f z}) = 1 := by
    calc
      Nat.card ({x : ℂ // f x = f z})
          = Nat.card ({x : ℂ // f x = y0}) := hcard_const (f z) y0
      _ = 1 := hy0
  have hfinite : ({x : ℂ | f x = f z} : Set ℂ).Finite :=
    finite_fiber_of_isProperMap_isLocallyInjective
      (f := f) hproper hlocal.isLocallyInjective (f z)
  haveI : Finite ({x : ℂ // f x = f z}) := hfinite.to_subtype
  letI : Fintype ({x : ℂ // f x = f z}) := Fintype.ofFinite ({x : ℂ // f x = f z})
  have hcardF : Fintype.card ({x : ℂ // f x = f z}) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hsub : Subsingleton ({x : ℂ // f x = f z}) := by
    apply (Fintype.card_le_one_iff_subsingleton).1
    simp [hcardF]
  have hs :
      (⟨z, rfl⟩ : {x : ℂ // f x = f z}) =
        (⟨w, hzw.symm⟩ : {x : ℂ // f x = f z}) :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hs

lemma natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s) (hfiberS : ∀ y, ({x : ℂ | f x = y} : Set ℂ) ⊆ s) :
    IsLocallyConstant (fun y : ℂ => Nat.card ({x : ℂ // f x = y})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro y
  have hfinite : ({x : ℂ | f x = y} : Set ℂ).Finite :=
    finite_fiber_of_isProperMap_isLocalHomeomorphOn_of_fiber_subset
      (f := f) hproper hlocal (y := y) (hfiberS y)
  rcases exists_open_natCard_fiber_eq_of_closedMap_localHomeomorphOn_of_open_of_finite_fiber_subset
      (f := f) (s := s) hproper.isClosedMap hlocal hsopen (y := y) (hfiberS y) hfinite with
    ⟨V, hVopen, hyV, hcard⟩
  refine ⟨V, hVopen, hyV, ?_⟩
  intro y' hy'
  exact hcard y' hy'

lemma natCard_fiber_eq_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s) (hfiberS : ∀ y, ({x : ℂ | f x = y} : Set ℂ) ⊆ s) :
    ∀ y y', Nat.card ({x : ℂ // f x = y}) = Nat.card ({x : ℂ // f x = y'}) := by
  have hloc :
      IsLocallyConstant (fun y : ℂ => Nat.card ({x : ℂ // f x = y})) :=
    natCard_fiber_isLocallyConstant_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset
      (f := f) (s := s) hproper hlocal hsopen hfiberS
  exact (IsLocallyConstant.iff_is_const (f := fun y : ℂ =>
    Nat.card ({x : ℂ // f x = y}))).1 hloc

lemma injective_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset_of_exists_natCard_fiber_eq_one
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s) (hfiberS : ∀ y, ({x : ℂ | f x = y} : Set ℂ) ⊆ s)
    (hdeg1 : ∃ y : ℂ, Nat.card ({x : ℂ // f x = y}) = 1) :
    Function.Injective f := by
  rcases hdeg1 with ⟨y0, hy0⟩
  have hcard_const := natCard_fiber_eq_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset
    (f := f) (s := s) hproper hlocal hsopen hfiberS
  intro z w hzw
  have hcard : Nat.card ({x : ℂ // f x = f z}) = 1 := by
    calc
      Nat.card ({x : ℂ // f x = f z})
          = Nat.card ({x : ℂ // f x = y0}) := hcard_const (f z) y0
      _ = 1 := hy0
  letI : Finite ({x : ℂ // f x = f z}) := by
    exact (finite_fiber_of_isProperMap_isLocalHomeomorphOn_of_fiber_subset
      (f := f) hproper hlocal (y := f z) (hfiberS (f z))).to_subtype
  letI : Fintype ({x : ℂ // f x = f z}) := Fintype.ofFinite ({x : ℂ // f x = f z})
  have hcardF : Fintype.card ({x : ℂ // f x = f z}) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hsub : Subsingleton ({x : ℂ // f x = f z}) := by
    apply (Fintype.card_le_one_iff_subsingleton).1
    simp [hcardF]
  have hs :
      (⟨z, rfl⟩ : {x : ℂ // f x = f z}) =
        (⟨w, hzw.symm⟩ : {x : ℂ // f x = f z}) :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hs

lemma natCard_fiber_isLocallyConstant_on_image_of_isProperMap_isLocalHomeomorphOn_of_open
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s)
    (hfiberS : ∀ y, y ∈ f '' s → ({x : ℂ | f x = y} : Set ℂ) ⊆ s) :
    IsLocallyConstant (fun y : f '' s => Nat.card ({x : ℂ // f x = y.1})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro y
  have hfinite : ({x : ℂ | f x = y.1} : Set ℂ).Finite :=
    finite_fiber_of_isProperMap_isLocalHomeomorphOn_of_fiber_subset
      (f := f) hproper hlocal (y := y.1) (hfiberS y.1 y.2)
  rcases exists_open_natCard_fiber_eq_of_closedMap_localHomeomorphOn_of_open_of_finite_fiber_subset
      (f := f) (s := s) hproper.isClosedMap hlocal hsopen (y := y.1)
      (hfiberS y.1 y.2) hfinite with
    ⟨V, hVopen, hyV, hcard⟩
  refine ⟨Subtype.val ⁻¹' V, hVopen.preimage continuous_subtype_val, ?_, ?_⟩
  · simpa using hyV
  · intro y' hy'
    exact hcard y'.1 hy'

lemma natCard_fiber_eq_on_image_of_isProperMap_isLocalHomeomorphOn_of_open_of_connected_image
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s) (hconn : IsConnected (f '' s))
    (hfiberS : ∀ y, y ∈ f '' s → ({x : ℂ | f x = y} : Set ℂ) ⊆ s) :
    ∀ y y' : f '' s, Nat.card ({x : ℂ // f x = y.1}) = Nat.card ({x : ℂ // f x = y'.1}) := by
  letI : PreconnectedSpace (f '' s) := Subtype.preconnectedSpace hconn.isPreconnected
  have hloc :
      IsLocallyConstant (fun y : f '' s => Nat.card ({x : ℂ // f x = y.1})) :=
    natCard_fiber_isLocallyConstant_on_image_of_isProperMap_isLocalHomeomorphOn_of_open
      (f := f) (s := s) hproper hlocal hsopen hfiberS
  exact (IsLocallyConstant.iff_is_const (f := fun y : f '' s =>
    Nat.card ({x : ℂ // f x = y.1}))).1 hloc

lemma injOn_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset_on_image_of_connected_image
    {f : ℂ → ℂ} {s : Set ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorphOn f s)
    (hsopen : IsOpen s) (hconn : IsConnected (f '' s))
    (hfiberS : ∀ y, y ∈ f '' s → ({x : ℂ | f x = y} : Set ℂ) ⊆ s)
    (hdeg1 : ∃ y : f '' s, Nat.card ({x : ℂ // f x = y.1}) = 1) :
    Set.InjOn f s := by
  intro z hz w hw hzw
  have hcard_const := natCard_fiber_eq_on_image_of_isProperMap_isLocalHomeomorphOn_of_open_of_connected_image
    (f := f) (s := s) hproper hlocal hsopen hconn hfiberS
  have hyz : f z ∈ f '' s := ⟨z, hz, rfl⟩
  let yz : f '' s := ⟨f z, hyz⟩
  rcases hdeg1 with ⟨y0, hy0⟩
  have hcard : Nat.card ({x : ℂ // f x = f z}) = 1 := by
    calc
      Nat.card ({x : ℂ // f x = f z})
          = Nat.card ({x : ℂ // f x = y0.1}) := hcard_const yz y0
      _ = 1 := hy0
  letI : Finite ({x : ℂ // f x = f z}) := by
    exact (finite_fiber_of_isProperMap_isLocalHomeomorphOn_of_fiber_subset
      (f := f) hproper hlocal (y := f z) (hfiberS (f z) hyz)).to_subtype
  letI : Fintype ({x : ℂ // f x = f z}) := Fintype.ofFinite ({x : ℂ // f x = f z})
  have hcardF : Fintype.card ({x : ℂ // f x = f z}) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hsub : Subsingleton ({x : ℂ // f x = f z}) := by
    apply (Fintype.card_le_one_iff_subsingleton).1
    simp [hcardF]
  have hs :
      (⟨z, rfl⟩ : {x : ℂ // f x = f z}) =
        (⟨w, hzw.symm⟩ : {x : ℂ // f x = f z}) :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hs

lemma natCard_fiber_eq_one_of_existsUnique
    {f : ℂ → ℂ} {y : ℂ} (huniq : ∃! x, f x = y) :
    Nat.card ({x : ℂ // f x = y}) = 1 := by
  rcases huniq with ⟨z, hz, hu⟩
  letI : Unique ({x : ℂ // f x = y}) := {
    default := ⟨z, hz⟩
    uniq := by
      intro a
      apply Subtype.ext
      exact (hu a.1 a.2)
  }
  letI : Fintype ({x : ℂ // f x = y}) := Fintype.ofFinite ({x : ℂ // f x = y})
  calc
    Nat.card ({x : ℂ // f x = y}) = Fintype.card ({x : ℂ // f x = y}) := by
      simp [Nat.card_eq_fintype_card]
    _ = 1 := Fintype.card_unique

lemma natCard_fiber_eq_one_of_injOn_of_mem_image_of_fiber_subset
    {f : ℂ → ℂ} {U : Set ℂ} {y : ℂ}
    (hUinj : Set.InjOn f U) (hyimg : y ∈ f '' U)
    (hfiberU : ({x : ℂ | f x = y} : Set ℂ) ⊆ U) :
    Nat.card ({x : ℂ // f x = y}) = 1 := by
  rcases hyimg with ⟨z, hzU, hzy⟩
  have huniq : ∃! x, f x = y := by
    refine ⟨z, hzy, ?_⟩
    intro x hx
    have hxU : x ∈ U := hfiberU (by simp [hx])
    exact hUinj hxU hzU (by simpa [hzy] using hx)
  exact natCard_fiber_eq_one_of_existsUnique (f := f) (y := y) huniq

lemma injective_of_isProperMap_isLocalHomeomorph_of_injOn_of_mem_image_of_fiber_subset
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f)
    {U : Set ℂ} {y : ℂ}
    (hUinj : Set.InjOn f U) (hyimg : y ∈ f '' U)
    (hfiberU : ({x : ℂ | f x = y} : Set ℂ) ⊆ U) :
    Function.Injective f := by
  have hdeg1 : ∃ y0 : ℂ, Nat.card ({x : ℂ // f x = y0}) = 1 := by
    refine ⟨y, ?_⟩
    exact natCard_fiber_eq_one_of_injOn_of_mem_image_of_fiber_subset
      (f := f) (U := U) (y := y) hUinj hyimg hfiberU
  exact injective_of_isProperMap_isLocalHomeomorph_of_exists_natCard_fiber_eq_one
    (f := f) hproper hlocal hdeg1

lemma bottcher_map_injective_of_proper_localHomeomorph_and_outside_seed
    (c : ℂ)
    (hproper : IsProperMap (Quadratic.bottcher_map c))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map c))
    (hUinj :
      Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2})
    {y : ℂ}
    (hyimg : y ∈ Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2})
    (hfiberU :
      ({z : ℂ | Quadratic.bottcher_map c z = y} : Set ℂ) ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Function.Injective (Quadratic.bottcher_map c) := by
  exact injective_of_isProperMap_isLocalHomeomorph_of_injOn_of_mem_image_of_fiber_subset
    (f := Quadratic.bottcher_map c) hproper hlocal hUinj hyimg hfiberU

lemma bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed
    (c : ℂ)
    (hproper : IsProperMap (Quadratic.bottcher_map c))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map c))
    (hUinj :
      Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2})
    {y : ℂ}
    (hyimg : y ∈ Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2})
    (hfiberU :
      ({z : ℂ | Quadratic.bottcher_map c z = y} : Set ℂ) ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  have hglobal :
      Function.Injective (Quadratic.bottcher_map c) :=
    bottcher_map_injective_of_proper_localHomeomorph_and_outside_seed c hproper hlocal
      hUinj hyimg hfiberU
  exact hglobal.injOn


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
  have hz' : ‖c‖ + 2 ≤ ‖z‖ := le_trans hR hz.1
  exact large_norm_mem_outside_disk c z hz'

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

lemma eventually_atInfinity_bottcher_map_div_mem_slitPlaneRight (c : ℂ) :
    ∀ᶠ z in atInfinity, (Quadratic.bottcher_map c z / z) ∈ Quadratic.slitPlaneRight := by
  have h := tendsto_bottcher_map_div_atInfinity c
  have h' : Tendsto (fun z => ‖(Quadratic.bottcher_map c z / z) - (1 : ℂ)‖)
      atInfinity (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 h)
  have hball : ∀ᶠ z in atInfinity, ‖(Quadratic.bottcher_map c z / z) - (1 : ℂ)‖ < 1 := by
    have hε :=
      (tendsto_def.1 h') (Metric.ball (0 : ℝ) 1)
        (by simpa using (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)))
    simpa [Metric.ball, Real.norm_eq_abs] using hε
  refine hball.mono ?_
  intro z hz
  have hslit : (Quadratic.bottcher_map c z / z) ∈ Complex.slitPlane :=
    mem_slitPlane_of_norm_sub_one_lt_one hz
  have hre : 0 < (Quadratic.bottcher_map c z / z).re :=
    re_pos_of_norm_sub_one_lt_one hz
  exact ⟨hslit, hre⟩

lemma bottcher_map_div_eq_real_scale_of_ne_zero (c z : ℂ) (hz : z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ Quadratic.bottcher_map c z / z = (r : ℂ) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ⟨Real.exp (Quadratic.green_function c z) / ‖z‖, div_pos (Real.exp_pos _) hzpos, ?_⟩
  have hznorm : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hdiv : (z / ‖z‖) / z = (1 : ℂ) / ‖z‖ := by
    field_simp [div_eq_mul_inv, hz, hznorm, mul_assoc, mul_comm, mul_left_comm]
  calc
    Quadratic.bottcher_map c z / z
        = ((z / ‖z‖) * (Real.exp (Quadratic.green_function c z) : ℂ)) / z := by
            simp [Quadratic.bottcher_map, hz]
    _ = (Real.exp (Quadratic.green_function c z) : ℂ) * ((z / ‖z‖) / z) := by
          ring
    _ = (Real.exp (Quadratic.green_function c z) : ℂ) * ((1 : ℂ) / ‖z‖) := by
          simp [hdiv]
    _ = ((Real.exp (Quadratic.green_function c z) / ‖z‖ : ℝ) : ℂ) := by
          simp [div_eq_mul_inv, mul_comm]

lemma bottcher_map_div_eq_real_scale_of_outside_open
    (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    ∃ r : ℝ, 0 < r ∧ Quadratic.bottcher_map c z / z = (r : ℂ) := by
  have hzpos : 0 < ‖z‖ := by
    linarith [hz, norm_nonneg c]
  have hz_ne : z ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt hzpos)
  exact bottcher_map_div_eq_real_scale_of_ne_zero c z hz_ne

lemma bottcher_map_div_mem_slitPlaneRight_of_ne_zero (c z : ℂ) (hz : z ≠ 0) :
    (Quadratic.bottcher_map c z / z) ∈ Quadratic.slitPlaneRight := by
  rcases bottcher_map_div_eq_real_scale_of_ne_zero c z hz with ⟨r, hrpos, hratio⟩
  have hslit : (Quadratic.bottcher_map c z / z) ∈ Complex.slitPlane := by
    have hslit' : (1 : ℂ) * (r : ℝ) ∈ Complex.slitPlane :=
      slitPlane_mul_of_real_pos (x := 1) Complex.one_mem_slitPlane r hrpos
    simpa [hratio] using hslit'
  have hre : 0 < (Quadratic.bottcher_map c z / z).re := by
    simpa [hratio] using hrpos
  exact ⟨hslit, hre⟩

lemma exists_bottcher_map_div_mem_slitPlaneRight_of_large_norm (c : ℂ) :
    ∃ S, ∀ z, S ≤ ‖z‖ → (Quadratic.bottcher_map c z / z) ∈ Quadratic.slitPlaneRight := by
  have h := eventually_atInfinity_bottcher_map_div_mem_slitPlaneRight c
  dsimp [atInfinity] at h
  have h' := (Filter.eventually_comap).1 h
  rcases (Filter.eventually_atTop.1 h') with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  intro z hz
  have := hS ‖z‖ hz z rfl
  simpa using this

lemma outside_open_subset_outside_disk (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ outside_disk c := by
  intro z hz
  have hz' : ‖z‖ > ‖c‖ + 2 := by simpa using hz
  exact large_norm_mem_outside_disk c z (le_of_lt hz')


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

lemma closedBall_subset_outside_open_of_large_norm
    (c z₀ : ℂ) (hlarge : 2 * (‖c‖ + 2) < ‖z₀‖) :
    Metric.closedBall z₀ (‖z₀‖ / 2) ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  intro z hz
  have hdist : dist z z₀ ≤ ‖z₀‖ / 2 := by
    simp [Metric.mem_closedBall] at hz
    exact hz
  have htri : ‖z₀‖ ≤ ‖z₀ - z‖ + ‖z‖ := by
    have h := norm_add_le (z₀ - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hle : ‖z₀‖ - ‖z₀ - z‖ ≤ ‖z‖ := by
    linarith
  have hnorm_sub : ‖z₀ - z‖ = dist z z₀ := by
    have h1 : dist z₀ z = ‖z₀ - z‖ := by simp [dist_eq_norm]
    have h2 : dist z₀ z = dist z z₀ := dist_comm _ _
    exact h1.trans h2
  have hge : ‖z‖ ≥ ‖z₀‖ - ‖z₀‖ / 2 := by
    have : ‖z₀ - z‖ ≤ ‖z₀‖ / 2 := by simpa [hnorm_sub] using hdist
    exact le_trans (by linarith) hle
  have hhalf : (‖z₀‖ - ‖z₀‖ / 2 : ℝ) = ‖z₀‖ / 2 := by
    ring
  have hge' : ‖z‖ ≥ ‖z₀‖ / 2 := by
    simp [hhalf] at hge
    exact hge
  have hlt : ‖c‖ + 2 < ‖z₀‖ / 2 := by
    nlinarith
  exact lt_of_lt_of_le hlt hge'


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

lemma bottcher_map_deriv_ne_zero_of_normalized
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hnorm : bottcher_normalized_at_infty c) :
    ∃ R, ∀ z, R ≤ ‖z‖ → deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  -- Use the normalization to control `bottcher_map c z - z` on large circles.
  have hbound := bottcher_map_minus_id_bound_of_normalized c hnorm
  rcases hbound (1 / 4) (by norm_num) with ⟨R0, hR0⟩
  let R1 : ℝ := max (2 * (‖c‖ + 2) + 1) (2 * R0)
  refine ⟨R1, ?_⟩
  intro z hz
  have hzlarge : 2 * (‖c‖ + 2) < ‖z‖ := by
    have : 2 * (‖c‖ + 2) + 1 ≤ R1 := le_max_left _ _
    have hz' : 2 * (‖c‖ + 2) + 1 ≤ ‖z‖ := le_trans this hz
    nlinarith
  have hzR0 : R0 ≤ ‖z‖ / 2 := by
    have : 2 * R0 ≤ R1 := le_max_right _ _
    have hz' : 2 * R0 ≤ ‖z‖ := le_trans this hz
    nlinarith
  let r : ℝ := ‖z‖ / 2
  have hrpos : 0 < r := by
    have hposR1 : 0 < R1 := by
      have hpos : 0 < 2 * (‖c‖ + 2) + 1 := by
        have hc : 0 ≤ ‖c‖ := norm_nonneg _
        nlinarith
      exact lt_of_lt_of_le hpos (le_max_left _ _)
    have hposz : 0 < ‖z‖ := lt_of_lt_of_le hposR1 hz
    have : 0 < ‖z‖ / 2 := by nlinarith [hposz]
    simpa [r] using this
  have hsubset :
      Metric.closedBall z r ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
    closedBall_subset_outside_open_of_large_norm c z (by simpa [r] using hzlarge)
  have hUopen : IsOpen {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
    simpa using (isOpen_lt continuous_const continuous_norm)
  have hUbasin : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ Quadratic.basin_of_infinity c := by
    intro w hw
    have hw' : w ∈ outside_disk c :=
      large_norm_mem_outside_disk c w (le_of_lt hw)
    exact outside_disk_subset_quadratic_basin c hw'
  have hdiff :
      DifferentiableOn ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
    bottcher_map_differentiableOn_open c _ hUopen hslit hUbasin
  have hDiff : DiffContOnCl ℂ (Quadratic.bottcher_map c) (Metric.ball z r) :=
    (hdiff.diffContOnCl_ball (hc := hsubset))
  have hC :
      ∀ w ∈ Metric.sphere z r, ‖Quadratic.bottcher_map c w - w‖ ≤ (1 / 4) * (‖z‖ + r) := by
    intro w hw
    have hw' : ‖w‖ ≥ r := by
      have hdist : dist w z = r := by
        simp at hw
        exact hw
      have htri : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        have h := norm_add_le (z - w) w
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      have hle : ‖z‖ - ‖z - w‖ ≤ ‖w‖ := by linarith
      have hnorm_sub : ‖z - w‖ = dist w z := by
        have h1 : dist z w = ‖z - w‖ := by simp [dist_eq_norm]
        have h2 : dist z w = dist w z := dist_comm _ _
        exact h1.trans h2
      have hge : ‖w‖ ≥ ‖z‖ - r := by
        have : ‖z - w‖ = r := by
          simp [hnorm_sub, hdist]
        nlinarith [hle, this]
      have hle' : ‖z‖ - r = r := by
        simp [r]; ring
      simpa [hle'] using hge
    have hwR0 : R0 ≤ ‖w‖ := by
      exact le_trans hzR0 hw'
    have hbd := hR0 w hwR0
    have hle' : (1 / 4 : ℝ) * ‖w‖ ≤ (1 / 4 : ℝ) * (‖z‖ + r) := by
      have : ‖w‖ ≤ ‖z‖ + r := by
        have hdist : dist w z = r := by
          simp at hw
          exact hw
        have htri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          have h := norm_add_le (w - z) z
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
        have hnorm_sub : dist w z = ‖w - z‖ := by
          simp [dist_eq_norm]
        nlinarith [htri, hdist, hnorm_sub]
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    exact hbd.trans hle'
  have hC' : ((1 / 4 : ℝ) * (‖z‖ + r)) / r < 1 := by
    have hposz : 0 < ‖z‖ := lt_of_lt_of_le (by
      have hpos : 0 < 2 * (‖c‖ + 2) + 1 := by
        have hc : 0 ≤ ‖c‖ := norm_nonneg _
        nlinarith
      exact lt_of_lt_of_le hpos (le_max_left _ _)) hz
    have hnorm_ne : ‖z‖ ≠ 0 := ne_of_gt hposz
    have hcalc : (‖z‖ + r) / r = 3 := by
      calc
        (‖z‖ + r) / r = (‖z‖ + ‖z‖ / 2) / (‖z‖ / 2) := by
          simp [r]
        _ = ((3 / 2 : ℝ) * ‖z‖) / (‖z‖ / 2) := by
          ring
        _ = 3 := by
          field_simp [hnorm_ne]
    have hcalc' : ((1 / 4 : ℝ) * (‖z‖ + r)) / r = (3 / 4 : ℝ) := by
      calc
        ((1 / 4 : ℝ) * (‖z‖ + r)) / r = (1 / 4 : ℝ) * ((‖z‖ + r) / r) := by
          ring
        _ = (1 / 4 : ℝ) * 3 := by simp [hcalc]
        _ = (3 / 4 : ℝ) := by ring
    have hlt' : ((1 / 4 : ℝ) * (‖z‖ + r)) / r < 1 := by
      calc
        ((1 / 4 : ℝ) * (‖z‖ + r)) / r = (3 / 4 : ℝ) := hcalc'
        _ < 1 := by norm_num
    exact hlt'
  exact deriv_ne_zero_of_sphere_bound (f := Quadratic.bottcher_map c) (z₀ := z)
    (R := r) hrpos hDiff hC hC'

lemma quadratic_map_norm_gt_outside
    (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    ‖quadratic_map c z‖ > ‖c‖ + 2 := by
  have hge : ‖quadratic_map c z‖ ≥ ‖z‖ + 1 :=
    quadratic_map_norm_ge_add_one c z (le_of_lt hz)
  have hlt : ‖z‖ + 1 > ‖c‖ + 2 := by
    nlinarith
  exact lt_of_lt_of_le hlt hge

lemma quadratic_map_maps_outside_open (c : ℂ) :
    MapsTo (quadratic_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  intro z hz
  exact quadratic_map_norm_gt_outside c z (by simpa using hz)

lemma bottcher_conj_deriv_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    {z : ℂ} (hz : ‖z‖ > ‖c‖ + 2) :
    deriv (Quadratic.bottcher_map c) (quadratic_map c z) * (2 * z) =
      2 * (Quadratic.bottcher_map c z) * deriv (Quadratic.bottcher_map c) z := by
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  have hzU : z ∈ U := by simpa [U] using hz
  have hzU' : quadratic_map c z ∈ U := by
    have : ‖quadratic_map c z‖ > ‖c‖ + 2 := quadratic_map_norm_gt_outside c z hz
    simpa [U] using this
  have hbasin : U ⊆ Quadratic.basin_of_infinity c := by
    intro w hw
    have hw' : w ∈ outside_disk c :=
      large_norm_mem_outside_disk c w (le_of_lt hw)
    exact outside_disk_subset_quadratic_basin c hw'
  have hφz : HasDerivAt (Quadratic.bottcher_map c)
      (deriv (Quadratic.bottcher_map c) z) z := by
    have h := (bottcher_map_analytic_on_outside c hslit) z hzU
    exact h.differentiableAt.hasDerivAt
  have hφfz : HasDerivAt (Quadratic.bottcher_map c)
      (deriv (Quadratic.bottcher_map c) (quadratic_map c z)) (quadratic_map c z) := by
    have h := (bottcher_map_analytic_on_outside c hslit) (quadratic_map c z) hzU'
    exact h.differentiableAt.hasDerivAt
  have hquad : HasDerivAt (fun w => quadratic_map c w) (2 * z) z := by
    simpa [quadratic_map, pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_pow (n := 2) z).add_const c
  have hcomp :
      HasDerivAt (fun w => Quadratic.bottcher_map c (quadratic_map c w))
        (deriv (Quadratic.bottcher_map c) (quadratic_map c z) * (2 * z)) z := by
    simpa using hφfz.comp z hquad
  have hpow :
      HasDerivAt (fun w => (Quadratic.bottcher_map c w) ^ 2)
        (2 * (Quadratic.bottcher_map c z) * deriv (Quadratic.bottcher_map c) z) z := by
    simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using hφz.pow 2
  have hEq : (fun w => Quadratic.bottcher_map c (quadratic_map c w))
      =ᶠ[𝓝 z] fun w => (Quadratic.bottcher_map c w) ^ 2 := by
    have hUmem : ∀ᶠ w in 𝓝 z, w ∈ U := by
      simpa using hUopen.mem_nhds (by simpa [U] using hz)
    refine hUmem.mono ?_
    intro w hw
    have hw' : w ∈ Quadratic.basin_of_infinity c := hbasin hw
    exact bottcher_conj_on_basin c w hw'
  have hcomp' :
      HasDerivAt (fun w => (Quadratic.bottcher_map c w) ^ 2)
        (deriv (Quadratic.bottcher_map c) (quadratic_map c z) * (2 * z)) z :=
    hcomp.congr_of_eventuallyEq hEq.symm
  exact (hpow.unique hcomp').symm

lemma deriv_zero_iter_of_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    {z : ℂ} (hz : ‖z‖ > ‖c‖ + 2) (hzero : deriv (Quadratic.bottcher_map c) z = 0) :
    ∀ n, deriv (Quadratic.bottcher_map c) ((quadratic_map c)^[n] z) = 0 := by
  intro n
  induction n with
  | zero =>
      simpa using hzero
  | succ n ih =>
      have hz' : ‖(quadratic_map c)^[n] z‖ > ‖c‖ + 2 := by
        have hge : ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n :=
          iterate_quadratic_map_norm_ge_add c z n (le_of_lt hz)
        nlinarith
      have hrel := bottcher_conj_deriv_on_outside c hslit (z := (quadratic_map c)^[n] z) hz'
      have hne : (2 * (quadratic_map c)^[n] z) ≠ 0 := by
        have hposc : (0 : ℝ) < ‖c‖ + 2 := by
          have hc : 0 ≤ ‖c‖ := norm_nonneg _
          nlinarith
        have hpos : 0 < ‖(quadratic_map c)^[n] z‖ := lt_trans hposc hz'
        exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (by
          exact (norm_ne_zero_iff).1 (ne_of_gt hpos)))
      have : deriv (Quadratic.bottcher_map c) ((quadratic_map c)^[n.succ] z) = 0 := by
        have hrel' :
            deriv (Quadratic.bottcher_map c) ((quadratic_map c)^[n.succ] z) * (2 * (quadratic_map c)^[n] z) =
              2 * (Quadratic.bottcher_map c ((quadratic_map c)^[n] z)) *
                deriv (Quadratic.bottcher_map c) ((quadratic_map c)^[n] z) := by
          simpa [Function.iterate_succ_apply'] using hrel
        have hrel'' :
            deriv (Quadratic.bottcher_map c) ((quadratic_map c)^[n.succ] z) * (2 * (quadratic_map c)^[n] z) =
              0 * (2 * (quadratic_map c)^[n] z) := by
          simpa [ih] using hrel'
        exact mul_right_cancel₀ hne hrel''
      simpa using this

lemma bottcher_map_deriv_ne_zero_on_outside_open_of_normalized
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hnorm : bottcher_normalized_at_infty c) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  rcases bottcher_map_deriv_ne_zero_of_normalized c hslit hnorm with ⟨R, hR⟩
  intro z hz hzero
  have hescape : Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
    have hz' : z ∈ outside_disk c :=
      large_norm_mem_outside_disk c z (le_of_lt hz)
    simpa [outside_disk, basin_of_infinity] using hz'
  have hlarge : ∀ᶠ n in atTop, R ≤ ‖(quadratic_map c)^[n] z‖ :=
    (tendsto_atTop.1 hescape) R
  rcases (Filter.eventually_atTop.1 hlarge) with ⟨N, hN⟩
  have hzeroN : deriv (Quadratic.bottcher_map c) ((quadratic_map c)^[N] z) = 0 :=
    (deriv_zero_iter_of_outside c hslit hz hzero) N
  have hcontr := hR ((quadratic_map c)^[N] z) (hN N (le_rfl))
  exact (hcontr hzeroN)

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

lemma bottcher_map_isLocalHomeomorphOn_outside_open_of_normalized
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hnorm : bottcher_normalized_at_infty c) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  refine bottcher_map_isLocalHomeomorphOn_outside_of_deriv_ne_zero c hslit ?_
  exact bottcher_map_deriv_ne_zero_on_outside_open_of_normalized c hslit hnorm

lemma bottcher_map_isLocalHomeomorphOn_outside_open
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  have hnorm := bottcher_normalized_at_infty_of_green c
  exact bottcher_map_isLocalHomeomorphOn_outside_open_of_normalized c hslit hnorm

lemma bottcher_map_isOpen_on_outside_of_normalized
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hnorm : bottcher_normalized_at_infty c) :
    ∀ t ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2}, IsOpen t →
      IsOpen (Quadratic.bottcher_map c '' t) := by
  intro t ht htop
  have hlocal := bottcher_map_isLocalHomeomorphOn_outside_open_of_normalized c hslit hnorm
  exact isOpen_image_of_isLocalHomeomorphOn hlocal t ht htop

lemma bottcher_map_isOpen_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    ∀ t ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2}, IsOpen t →
      IsOpen (Quadratic.bottcher_map c '' t) := by
  intro t ht htop
  have hlocal := bottcher_map_isLocalHomeomorphOn_outside_open c hslit
  exact isOpen_image_of_isLocalHomeomorphOn hlocal t ht htop

lemma bottcher_map_isOpenMap_on_outside_open
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    IsOpenMap (fun z : {z : ℂ | ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z) := by
  intro t ht
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  rcases isOpen_induced_iff.mp ht with ⟨u, hu, rfl⟩
  have hopen_image :
      IsOpen (Quadratic.bottcher_map c '' (u ∩ U)) := by
    refine bottcher_map_isOpen_on_outside c hslit (t := u ∩ U) ?_ (hu.inter hUopen)
    exact Set.inter_subset_right
  have himage :
      (fun z : {z : ℂ | ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z) ''
          (Subtype.val ⁻¹' u) =
        Quadratic.bottcher_map c '' (u ∩ U) := by
    calc
      (fun z : {z : ℂ | ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z) ''
          (Subtype.val ⁻¹' u)
          = Quadratic.bottcher_map c '' (Subtype.val '' (Subtype.val ⁻¹' u)) := by
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
              · rintro ⟨x, hx, rfl⟩
                rcases hx with ⟨x', hx', rfl⟩
                exact ⟨x', hx', rfl⟩
      _ = Quadratic.bottcher_map c '' (u ∩ U) := by
            simp [U, Subtype.image_preimage_coe, Set.inter_comm]
  simpa [himage] using hopen_image

/-- Derivative nonvanishing on outside-open from local analyticity plus
outside-open injectivity. -/
lemma bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  intro z hz
  let U : Set ℂ := {w : ℂ | ‖w‖ > ‖c‖ + 2}
  have hzU : z ∈ U := by simpa [U] using hz
  have hf : AnalyticAt ℂ (Quadratic.bottcher_map c) z :=
    hanalytic z hz
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  have hUnhds : U ∈ 𝓝 z := hUopen.mem_nhds hzU
  have h_injU : Set.InjOn (Quadratic.bottcher_map c) U := by
    simpa [U] using h_inj
  exact deriv_ne_zero_of_injOn_nhds hf U hUnhds h_injU

/-- Local-homeomorph on outside-open from local analyticity plus outside-open
injectivity. -/
lemma bottcher_map_isLocalHomeomorphOn_outside_open_of_analyticAt_of_injOn
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  refine isLocalHomeomorphOn_of_analytic_deriv_ne_zero ?_ ?_
  · intro z hz
    exact hanalytic z (by simpa using hz)
  · intro z hz
    exact bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn
      c hanalytic h_inj z (by simpa using hz)

/-- Local-homeomorph on outside-open from local analyticity plus derivative
nonvanishing on outside-open. -/
lemma bottcher_map_isLocalHomeomorphOn_outside_open_of_analyticAt_of_deriv_ne_zero
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (hderiv : ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  refine isLocalHomeomorphOn_of_analytic_deriv_ne_zero ?_ ?_
  · intro z hz
    exact hanalytic z (by simpa using hz)
  · intro z hz
    exact hderiv z (by simpa using hz)

/-- Open-map-on-subtype variant from local analyticity and outside-open
injectivity. -/
lemma bottcher_map_isOpenMap_on_outside_open_of_analyticAt_of_injOn
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    IsOpenMap (fun z : {z : ℂ | ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z) := by
  intro t ht
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  rcases isOpen_induced_iff.mp ht with ⟨u, hu, rfl⟩
  have hlocal :
      IsLocalHomeomorphOn (Quadratic.bottcher_map c) U :=
    bottcher_map_isLocalHomeomorphOn_outside_open_of_analyticAt_of_injOn
      c hanalytic (by simpa [U] using h_inj)
  have hopen_image :
      IsOpen (Quadratic.bottcher_map c '' (u ∩ U)) := by
    refine isOpen_image_of_isLocalHomeomorphOn hlocal (u ∩ U) ?_ (hu.inter hUopen)
    exact Set.inter_subset_right
  have himage :
      (fun z : {z : ℂ | ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z) ''
          (Subtype.val ⁻¹' u) =
        Quadratic.bottcher_map c '' (u ∩ U) := by
    calc
      (fun z : {z : ℂ | ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z) ''
          (Subtype.val ⁻¹' u)
          = Quadratic.bottcher_map c '' (Subtype.val '' (Subtype.val ⁻¹' u)) := by
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
              · rintro ⟨x, hx, rfl⟩
                rcases hx with ⟨x', hx', rfl⟩
                exact ⟨x', hx', rfl⟩
      _ = Quadratic.bottcher_map c '' (u ∩ U) := by
            simp [U, Subtype.image_preimage_coe, Set.inter_comm]
  simpa [himage] using hopen_image

lemma bottcher_map_image_outside_open_isOpen
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    IsOpen (Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2}) := by
  have hopen : IsOpen {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
    simpa using (isOpen_lt continuous_const continuous_norm)
  have h :=
    bottcher_map_isOpen_on_outside c hslit
      (t := {z : ℂ | ‖z‖ > ‖c‖ + 2})
      (by intro z hz; exact hz) hopen
  simpa using h

lemma bottcher_map_image_outside_open_subset_outside_disk
    (c : ℂ) :
    Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆
      Quadratic.bottcher_map c '' outside_disk c := by
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  exact ⟨z, outside_open_subset_outside_disk c hz, rfl⟩

lemma bottcher_map_image_outside_disk_subset_exterior (c : ℂ) :
    Quadratic.bottcher_map c '' outside_disk c ⊆ {w : ℂ | 1 < ‖w‖} := by
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  exact bottcher_map_norm_gt_one_of_outside c hz

lemma isPathConnected_exterior : IsPathConnected {w : ℂ | 1 < ‖w‖} := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    simp [Complex.rank_real_complex]
  have hpc : IsPathConnected ({0}ᶜ : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : ℂ)
  let f : ℂ → ℂ := fun z => ((1 + ‖z‖) / ‖z‖ : ℝ) • z
  have hf : ContinuousOn f ({0}ᶜ : Set ℂ) := by
    have hnum : ContinuousOn (fun z : ℂ => (1 : ℝ) + ‖z‖) ({0}ᶜ : Set ℂ) :=
      (continuous_const.add continuous_norm).continuousOn
    have hden : ContinuousOn (fun z : ℂ => ‖z‖) ({0}ᶜ : Set ℂ) :=
      continuous_norm.continuousOn
    have hden0 : ∀ z ∈ ({0}ᶜ : Set ℂ), (‖z‖ : ℝ) ≠ 0 := by
      intro z hz
      exact (norm_ne_zero_iff).2 (by simpa using hz)
    have hdiv :
        ContinuousOn (fun z : ℂ => ((1 : ℝ) + ‖z‖) / ‖z‖) ({0}ᶜ : Set ℂ) :=
      ContinuousOn.div hnum hden hden0
    simpa [f] using (ContinuousOn.smul hdiv continuous_id.continuousOn)
  have himage : f '' ({0}ᶜ : Set ℂ) = {w : ℂ | 1 < ‖w‖} := by
    refine subset_antisymm ?_ ?_
    · intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      have hz0 : z ≠ 0 := by simpa using hz
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hrpos : 0 < ((1 + ‖z‖) / ‖z‖ : ℝ) := by
        have hnum : 0 < 1 + ‖z‖ := by nlinarith
        exact div_pos hnum hzpos
      have hnorm :
          ‖((1 + ‖z‖) / ‖z‖ : ℝ) • z‖ =
            ((1 + ‖z‖) / ‖z‖) * ‖z‖ := by
        have hrnonneg : 0 ≤ ((1 + ‖z‖) / ‖z‖ : ℝ) := le_of_lt hrpos
        simpa using (norm_smul_of_nonneg hrnonneg z)
      have hmul : ((1 + ‖z‖) / ‖z‖) * ‖z‖ = 1 + ‖z‖ := by
        field_simp [ne_of_gt hzpos]
      have hgt' : 1 < ((1 + ‖z‖) / ‖z‖) * ‖z‖ := by
        have : 1 < 1 + ‖z‖ := by nlinarith
        simpa [hmul] using this
      have hgt : 1 < ‖f z‖ := by
        have hnormf : ((1 + ‖z‖) / ‖z‖) * ‖z‖ = ‖f z‖ := by
          simpa [f] using hnorm.symm
        exact lt_of_lt_of_eq hgt' hnormf
      exact hgt
    · intro w hw
      have hwpos : 0 < ‖w‖ := lt_trans (by norm_num) hw
      let z : ℂ := ((‖w‖ - 1) / ‖w‖ : ℝ) • w
      have hcoefpos : 0 < ((‖w‖ - 1) / ‖w‖ : ℝ) := by
        have hnum : 0 < ‖w‖ - 1 := sub_pos.mpr hw
        exact div_pos hnum hwpos
      have hcoefne : ((‖w‖ - 1) / ‖w‖ : ℝ) ≠ 0 := by
        exact ne_of_gt hcoefpos
      have hw0 : w ≠ 0 := by
        exact (norm_ne_zero_iff).1 (ne_of_gt hwpos)
      have hz0 : z ≠ 0 := by
        intro hz
        have : ((‖w‖ - 1) / ‖w‖ : ℝ) = 0 ∨ w = 0 := by
          simpa [z] using (smul_eq_zero.mp hz)
        cases this with
        | inl h => exact hcoefne h
        | inr h => exact hw0 h
      have hzmem : z ∈ ({0}ᶜ : Set ℂ) := by
        simpa using hz0
      have hnormz :
          ‖z‖ = ‖w‖ - 1 := by
        have hnormz' :
            ‖z‖ = ((‖w‖ - 1) / ‖w‖) * ‖w‖ := by
          have hcoefnonneg : 0 ≤ ((‖w‖ - 1) / ‖w‖ : ℝ) := le_of_lt hcoefpos
          simpa [z] using (norm_smul_of_nonneg hcoefnonneg w)
        have hmul : ((‖w‖ - 1) / ‖w‖) * ‖w‖ = ‖w‖ - 1 := by
          field_simp [ne_of_gt hwpos]
        exact hnormz'.trans hmul
      have hcoef :
          ((1 + ‖z‖) / ‖z‖ : ℝ) * ((‖w‖ - 1) / ‖w‖) = 1 := by
        have hpos : 0 < ‖w‖ - 1 := sub_pos.mpr hw
        calc
          ((1 + ‖z‖) / ‖z‖) * ((‖w‖ - 1) / ‖w‖)
              = ((1 + (‖w‖ - 1)) / (‖w‖ - 1)) * ((‖w‖ - 1) / ‖w‖) := by
                  simp [hnormz]
          _ = (‖w‖ / (‖w‖ - 1)) * ((‖w‖ - 1) / ‖w‖) := by ring
          _ = 1 := by
                field_simp [ne_of_gt hwpos, ne_of_gt hpos]
      refine ⟨z, hzmem, ?_⟩
      calc
        f z = ((1 + ‖z‖) / ‖z‖ : ℝ) • z := rfl
        _ = ((1 + ‖z‖) / ‖z‖ : ℝ) • (((‖w‖ - 1) / ‖w‖ : ℝ) • w) := by
              simp [z]
        _ = (((1 + ‖z‖) / ‖z‖ : ℝ) * ((‖w‖ - 1) / ‖w‖)) • w := by
              simp [mul_assoc]
        _ = (1 : ℝ) • w := by
              simp [hcoef]
        _ = w := by simp
  simpa [himage] using hpc.image' hf

lemma isConnected_exterior : IsConnected {w : ℂ | 1 < ‖w‖} := by
  exact isPathConnected_exterior.isConnected

lemma bottcher_map_image_outside_disk_eq_exterior_of_preimage
    (c : ℂ)
    (hpre : (Quadratic.bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c) :
    Quadratic.bottcher_map c '' outside_disk c = {w : ℂ | 1 < ‖w‖} := by
  refine subset_antisymm (bottcher_map_image_outside_disk_subset_exterior c) ?_
  intro w hw
  rcases (Quadratic.bottcher_map_surj c w hw) with ⟨z, hzdom, rfl⟩
  have hzpre : z ∈ (Quadratic.bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} := by
    have hw' : 1 < ‖Quadratic.bottcher_map c z‖ := by
      simpa using hw
    simp [Set.preimage, hw']
  exact ⟨z, hpre hzpre, rfl⟩

lemma bottcher_map_image_outside_disk_eq_exterior
    (c : ℂ)
    (hpre : (Quadratic.bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c) :
    Quadratic.bottcher_map c '' outside_disk c = {w : ℂ | 1 < ‖w‖} := by
  exact bottcher_map_image_outside_disk_eq_exterior_of_preimage c hpre

lemma bottcher_preimage_exterior_subset_outside_of_inj
    (c : ℂ) (hinj : Function.Injective (Quadratic.bottcher_map c))
    (himage : Quadratic.bottcher_map c '' outside_disk c = {w : ℂ | 1 < ‖w‖}) :
    (Quadratic.bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c := by
  intro z hz
  have hz' : Quadratic.bottcher_map c z ∈ {w : ℂ | 1 < ‖w‖} := by
    simpa [Set.preimage] using hz
  have hz'' : Quadratic.bottcher_map c z ∈ Quadratic.bottcher_map c '' outside_disk c := by
    simpa [himage] using hz'
  rcases hz'' with ⟨z0, hz0, hEq⟩
  have hz0' : z = z0 := hinj (by simp [hEq])
  subst hz0'
  exact hz0


lemma bottcher_map_local_inj_on_outside_open_of_normalized
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c)
    (hnorm : bottcher_normalized_at_infty c) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → ∃ s ∈ 𝓝 z, Set.InjOn (Quadratic.bottcher_map c) s := by
  intro z hz
  have hf : AnalyticAt ℂ (Quadratic.bottcher_map c) z :=
    (bottcher_map_analytic_on_outside c hslit) z (by simpa using hz)
  have hderiv : deriv (Quadratic.bottcher_map c) z ≠ 0 :=
    bottcher_map_deriv_ne_zero_on_outside_open_of_normalized c hslit hnorm z hz
  exact injOn_nhds_of_analyticAt hf hderiv

lemma bottcher_map_local_inj_on_outside_open
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → ∃ s ∈ 𝓝 z, Set.InjOn (Quadratic.bottcher_map c) s := by
  intro z hz
  have hnorm := bottcher_normalized_at_infty_of_green c
  exact bottcher_map_local_inj_on_outside_open_of_normalized c hslit hnorm z hz

lemma basin_escape_outside_open (c : ℂ) :
    ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  intro z hz
  have h := (tendsto_atTop.1 hz) (‖c‖ + 2 + 1)
  rcases (Filter.eventually_atTop.1 h) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hle : ‖c‖ + 2 + 1 ≤ ‖(quadratic_map c)^[N] z‖ := hN N (le_rfl)
  have hlt : ‖c‖ + 2 < ‖(quadratic_map c)^[N] z‖ := by
    linarith
  simpa using hlt

lemma bottcher_left_inv_outside_open_of_local_of_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) :
    ∀ z, ‖z‖ > ‖c‖ + 2 →
      Quadratic.external_ray_map_of_data h_data (Quadratic.bottcher_map c z) = z := by
  intro z hz
  exact Quadratic.external_ray_map_left_inverse_outside_open_of_data h_data z hz

lemma bottcher_left_inv_outside_open_of_local
    (c : ℂ) :
    ∀ z, ‖z‖ > ‖c‖ + 2 →
      Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z := by
  intro z hz
  simpa [Quadratic.external_ray_map] using
    bottcher_left_inv_outside_open_of_local_of_data (Quadratic.external_ray_map_data c) z hz

/-- Seam target: a left inverse of `bottcher_map` on outside-open. -/
def BottcherLeftInverseOnOutsideOpenData (c : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, ∀ z, ‖z‖ > ‖c‖ + 2 → g (Quadratic.bottcher_map c z) = z

/-- Seam target: a right inverse of `bottcher_map` on the exterior
    `{w | 1 < ‖w‖}`. -/
def BottcherRightInverseOnExteriorDataOutsidePlan (c : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, ∀ w, 1 < ‖w‖ → Quadratic.bottcher_map c (f w) = w

/-- Build outside-plan right-inverse seam data from explicit external-ray
    data. -/
lemma bottcher_right_inverse_on_exterior_data_of_external_ray_map_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) :
    BottcherRightInverseOnExteriorDataOutsidePlan c := by
  refine ⟨Quadratic.external_ray_map_of_data h_data, ?_⟩
  intro w hw
  exact Quadratic.external_ray_map_of_data_right_inverse h_data w hw

/-- Build outside-plan right-inverse seam data from exterior surjectivity of
    `bottcher_map` (through `bottcher_domain`). -/
lemma bottcher_right_inverse_on_exterior_data_of_bottcher_map_surj
    (c : ℂ) :
    BottcherRightInverseOnExteriorDataOutsidePlan c := by
  classical
  refine ⟨fun w => if hw : 1 < ‖w‖ then Classical.choose (Quadratic.bottcher_map_surj c w hw) else 0, ?_⟩
  intro w hw
  have hchoose :
      Quadratic.bottcher_map c (Classical.choose (Quadratic.bottcher_map_surj c w hw)) = w := by
    exact (Classical.choose_spec (Quadratic.bottcher_map_surj c w hw)).2
  simpa [hw] using hchoose

/-- Default outside-plan right-inverse seam data. -/
lemma bottcher_right_inverse_on_exterior_data (c : ℂ) :
    BottcherRightInverseOnExteriorDataOutsidePlan c := by
  exact bottcher_right_inverse_on_exterior_data_of_bottcher_map_surj c

/-- Any outside-open left-inverse payload yields outside-open injectivity. -/
lemma bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open
    (c : ℂ) (h_left : BottcherLeftInverseOnOutsideOpenData c) :
    Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  rcases h_left with ⟨g, hg⟩
  intro z hz w hw hzw
  have hz' : g (Quadratic.bottcher_map c z) = z := hg z hz
  have hw' : g (Quadratic.bottcher_map c w) = w := hg w hw
  have h := congrArg g hzw
  simpa [hz', hw'] using h

/-- Build outside-open left-inverse payload from explicit external-ray data. -/
lemma bottcher_left_inverse_on_outside_open_data_of_external_ray_map_data
    {c : ℂ} (h_data : Quadratic.ExternalRayMapData c) :
    BottcherLeftInverseOnOutsideOpenData c := by
  refine ⟨Quadratic.external_ray_map_of_data h_data, ?_⟩
  intro z hz
  exact Quadratic.external_ray_map_left_inverse_outside_open_of_data h_data z hz

/-- M5 target: surjectivity of `bottcher_map` onto the exterior by preimages in
    the outside-open seed region. -/
def BottcherSurjOnExteriorFromOutsideOpen (c : ℂ) : Prop :=
  ∀ w, 1 < ‖w‖ → ∃ z, ‖z‖ > ‖c‖ + 2 ∧ Quadratic.bottcher_map c z = w

/-- Alternative M5 target: the image of outside-open under `bottcher_map` is
    exactly the exterior. -/
def BottcherImageOutsideOpenIsExterior (c : ℂ) : Prop :=
  Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2} = {w : ℂ | 1 < ‖w‖}

/-- Image-equality target reduced to a single inclusion obligation:
    `exterior ⊆ image(outside-open)`. The reverse inclusion is automatic from
    the norm estimate on outside points. -/
theorem bottcherImageOutsideOpenIsExterior_iff_exterior_subset_image
    (c : ℂ) :
    BottcherImageOutsideOpenIsExterior c ↔
      ({w : ℂ | 1 < ‖w‖} ⊆
        Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2}) := by
  constructor
  · intro h_img w hw
    rw [h_img]
    exact hw
  · intro h_sub
    apply Set.Subset.antisymm
    · intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      exact bottcher_map_norm_gt_one_of_outside c (outside_open_subset_outside_disk c hz)
    · exact h_sub

/-- `c = 2` specialization of the previous reduction theorem. -/
theorem bottcherImageOutsideOpenIsExterior_two_iff_exterior_subset_image :
    BottcherImageOutsideOpenIsExterior (2 : ℂ) ↔
      ({w : ℂ | 1 < ‖w‖} ⊆
        Quadratic.bottcher_map (2 : ℂ) '' {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) := by
  exact bottcherImageOutsideOpenIsExterior_iff_exterior_subset_image (2 : ℂ)

/-- Named `c = 2` inclusion target for the outside-open image step. -/
def BottcherExteriorSubsetImageOutsideOpenTwo : Prop :=
  ({w : ℂ | 1 < ‖w‖} ⊆
    Quadratic.bottcher_map (2 : ℂ) '' {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2})

/-- Exterior points are always in the image of `outside_disk` under
    `bottcher_map`. This is unconditional in the current model because
    `outside_disk = basin_of_infinity`. -/
theorem exterior_subset_image_outside_disk_of_right_inverse
    (c : ℂ)
    (h_right : BottcherRightInverseOnExteriorDataOutsidePlan c) :
    ({w : ℂ | 1 < ‖w‖} ⊆ Quadratic.bottcher_map c '' outside_disk c) := by
  intro w hw
  rcases h_right with ⟨f, hf⟩
  refine ⟨f w, ?_, hf w hw⟩
  have hnorm : 1 < ‖Quadratic.bottcher_map c (f w)‖ := by
    simpa [hf w hw] using hw
  have hbasin : f w ∈ Quadratic.basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := f w) hnorm
  simpa [outside_disk] using hbasin

/-- Exterior points are always in the image of `outside_disk` under
    `bottcher_map`. This is unconditional in the current model because
    `outside_disk = basin_of_infinity`. -/
theorem exterior_subset_image_outside_disk (c : ℂ) :
    ({w : ℂ | 1 < ‖w‖} ⊆ Quadratic.bottcher_map c '' outside_disk c) := by
  intro w hw
  rcases Quadratic.bottcher_map_surj c w hw with ⟨z, _hz_dom, hzw⟩
  refine ⟨z, ?_, hzw⟩
  have hnorm : 1 < ‖Quadratic.bottcher_map c z‖ := by
    simpa [hzw] using hw
  have hbasin : z ∈ Quadratic.basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := z) hnorm
  simpa [outside_disk] using hbasin

/-- Intermediate reduction target: every outside-disk point has an
    outside-open point with the same Böttcher image. -/
def BottcherOutsideDiskToOutsideOpenImageRefinement (c : ℂ) : Prop :=
  ∀ z, z ∈ outside_disk c →
    ∃ u, ‖u‖ > ‖c‖ + 2 ∧
      Quadratic.bottcher_map c u = Quadratic.bottcher_map c z

/-- Outside-open exterior inclusion follows from the refinement target above. -/
theorem exterior_subset_image_outside_open_of_outside_disk_refinement_of_exterior_subset_image_outside_disk
    (c : ℂ)
    (h_disk : {w : ℂ | 1 < ‖w‖} ⊆ Quadratic.bottcher_map c '' outside_disk c)
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement c) :
    ({w : ℂ | 1 < ‖w‖} ⊆
      Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2}) := by
  intro w hw
  rcases h_disk hw with ⟨z, hz, hzw⟩
  rcases h_refine z hz with ⟨u, hu, hEq⟩
  exact ⟨u, hu, by simpa [hzw] using hEq⟩

/-- Outside-open exterior inclusion from a right-inverse-on-exterior payload
    plus outside-disk-to-outside-open image refinement. -/
theorem exterior_subset_image_outside_open_of_right_inverse_and_outside_disk_refinement
    (c : ℂ)
    (h_right : BottcherRightInverseOnExteriorDataOutsidePlan c)
    (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement c) :
    ({w : ℂ | 1 < ‖w‖} ⊆
      Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2}) := by
  exact exterior_subset_image_outside_open_of_outside_disk_refinement_of_exterior_subset_image_outside_disk
    c (exterior_subset_image_outside_disk_of_right_inverse c h_right) h_refine

/-- Outside-open exterior inclusion follows from the refinement target above. -/
theorem exterior_subset_image_outside_open_of_outside_disk_refinement
    (c : ℂ) (h_refine : BottcherOutsideDiskToOutsideOpenImageRefinement c) :
    ({w : ℂ | 1 < ‖w‖} ⊆
      Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2}) := by
  exact exterior_subset_image_outside_open_of_right_inverse_and_outside_disk_refinement c
    (bottcher_right_inverse_on_exterior_data c)
    h_refine

/-- Converse direction: outside-open exterior inclusion yields the refinement
    target on `outside_disk`. -/
theorem outside_disk_to_outside_open_image_refinement_of_exterior_subset_image_outside_open
    (c : ℂ)
    (h_sub : {w : ℂ | 1 < ‖w‖} ⊆
      Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    BottcherOutsideDiskToOutsideOpenImageRefinement c := by
  intro z hz
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c hz
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    green_function_pos_of_basin c z hz_basin
  have hw : 1 < ‖Quadratic.bottcher_map c z‖ :=
    bottcher_map_norm_gt_one_of_basin c z hz_basin hpos
  rcases h_sub hw with ⟨u, hu, hEq⟩
  exact ⟨u, hu, hEq⟩

/-- Stronger landing target: exterior rays land in outside-open. -/
def ExternalRayLandsOutsideOpen (c : ℂ) : Prop :=
  ∀ w, 1 < ‖w‖ → ‖Quadratic.external_ray_map c w‖ > ‖c‖ + 2

/-- Böttcher map restricted to outside-open, codomain restricted to the
exterior. -/
noncomputable def bottcher_map_outside_open_to_exterior (c : ℂ) :
    {z : ℂ // ‖z‖ > ‖c‖ + 2} → {w : ℂ // 1 < ‖w‖} := by
  intro z
  refine ⟨Quadratic.bottcher_map c z.1, ?_⟩
  exact bottcher_map_norm_gt_one_of_outside c
    (outside_open_subset_outside_disk c z.2)

/-- Image of a preimage set for the restricted outside-open map, expressed back
in ambient coordinates. -/
lemma image_preimage_bottcher_map_outside_open_to_exterior
    (c : ℂ) (K : Set {w : ℂ // 1 < ‖w‖}) :
    ((↑) '' ((bottcher_map_outside_open_to_exterior c) ⁻¹' K) : Set ℂ) =
      {z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
        Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    exact ⟨bottcher_map_outside_open_to_exterior c x, hx, rfl⟩
  · intro hz
    rcases hz with ⟨hz_out, y, hyK, hyEq⟩
    refine ⟨⟨z, hz_out⟩, ?_, rfl⟩
    have hEq :
        bottcher_map_outside_open_to_exterior c ⟨z, hz_out⟩ = y := by
      apply Subtype.ext
      simpa [bottcher_map_outside_open_to_exterior] using hyEq.symm
    simpa [hEq] using hyK

/-- Compactness of preimages under the restricted outside-open map translated to
an ambient compactness goal. -/
lemma isCompact_preimage_bottcher_map_outside_open_to_exterior_iff
    (c : ℂ) (K : Set {w : ℂ // 1 < ‖w‖}) :
    IsCompact ((bottcher_map_outside_open_to_exterior c) ⁻¹' K) ↔
      IsCompact
        ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) := by
  rw [Subtype.isCompact_iff, image_preimage_bottcher_map_outside_open_to_exterior]

/-- Continuity of the outside-open restricted Böttcher map from outside-open
`AnalyticAt` payload. -/
lemma continuous_bottcher_map_outside_open_restrict_of_analyticAt
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z) :
    Continuous (fun z : {z : ℂ // ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z.1) := by
  exact (continuousOn_iff_continuous_restrict).1 (by
    intro z hz
    exact (hanalytic z hz).continuousAt.continuousWithinAt)

/-- Properness of the restricted outside-open map is reduced to one ambient
compact-preimage obligation. -/
lemma isProperMap_bottcher_map_outside_open_to_exterior_of_preimage_compact
    (c : ℂ)
    (hcont : Continuous (fun z : {z : ℂ // ‖z‖ > ‖c‖ + 2} => Quadratic.bottcher_map c z.1))
    (hpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsCompact ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior c) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨?_, ?_⟩
  · exact hcont.codRestrict (by
      intro z
      exact bottcher_map_norm_gt_one_of_outside c
        (outside_open_subset_outside_disk c z.2))
  · intro K hK
    rw [isCompact_preimage_bottcher_map_outside_open_to_exterior_iff]
    exact hpre K hK

/-- Properness of the restricted outside-open map from outside-open analyticity
plus the ambient compact-preimage obligation. -/
lemma isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_compact
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (hpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsCompact ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior c) :=
  isProperMap_bottcher_map_outside_open_to_exterior_of_preimage_compact c
    (continuous_bottcher_map_outside_open_restrict_of_analyticAt c hanalytic) hpre

/-- `c = 2` specialization: properness of the restricted outside-open map from
outside-open analyticity plus the ambient compact-preimage obligation. -/
lemma isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_compact
    (hanalytic : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (hpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsCompact ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
          Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
  isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_compact
    (2 : ℂ) hanalytic hpre

/-- Compactness of restricted-map preimages follows from closedness of the
ambient outside-open preimage set; boundedness is provided by
`preimage_closedBall_bounded`. -/
lemma isCompact_preimage_bottcher_map_outside_open_to_exterior_of_isClosed
    (c : ℂ) (K : Set {w : ℂ // 1 < ‖w‖}) (hK : IsCompact K)
    (hclosed :
      IsClosed
        ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsCompact ((bottcher_map_outside_open_to_exterior c) ⁻¹' K) := by
  have hKbounded : Bornology.IsBounded (((↑) '' K : Set ℂ)) := by
    exact hK.image continuous_subtype_val |>.isBounded
  rcases hKbounded.subset_closedBall (0 : ℂ) with ⟨R, hR⟩
  rcases preimage_closedBall_bounded c R with ⟨S, hS⟩
  have hsubset_ball :
      ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
        Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) ⊆
        Metric.closedBall (0 : ℂ) S := by
    intro z hz
    have hzR : ‖Quadratic.bottcher_map c z‖ ≤ R := by
      have hzmem : Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ) := hz.2
      have : Quadratic.bottcher_map c z ∈ Metric.closedBall (0 : ℂ) R := hR hzmem
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    have hzS : ‖z‖ ≤ S := hS hzR
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzS
  have hbounded :
      Bornology.IsBounded
        ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := S)).subset hsubset_ball
  have hcompactAmbient :
      IsCompact
        ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hclosed, hbounded⟩
  rw [isCompact_preimage_bottcher_map_outside_open_to_exterior_iff]
  exact hcompactAmbient

/-- Properness of the restricted outside-open map from outside-open analyticity
plus closedness of ambient preimage sets against compact exterior targets. -/
lemma isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_closed
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
            Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior c) :=
  isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_compact c
    hanalytic (fun K hK =>
      isCompact_preimage_bottcher_map_outside_open_to_exterior_iff c K |>.1
        (isCompact_preimage_bottcher_map_outside_open_to_exterior_of_isClosed c K hK
          (hclosedpre K hK)))

/-- `c = 2` specialization: properness of the restricted outside-open map from
outside-open analyticity plus closedness of ambient preimage sets against
compact exterior targets. -/
lemma isProperMap_bottcher_map_outside_open_to_exterior_two_of_analyticAt_of_preimage_closed
    (hanalytic : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (hclosedpre :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        IsClosed
          ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2 ∧
            Quadratic.bottcher_map (2 : ℂ) z ∈ ((↑) '' K : Set ℂ)} : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) :=
  isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_closed
    (2 : ℂ) hanalytic hclosedpre

/-- Closedness of outside-open preimages against compact exterior targets from a
boundary-exclusion condition on `‖z‖ = ‖c‖ + 2`. -/
lemma isClosed_outside_open_preimage_image_compact_of_boundary_exclusion
    (c : ℂ) (K : Set {w : ℂ // 1 < ‖w‖}) (hK : IsCompact K)
    (hboundary :
      ∀ z, ‖z‖ = ‖c‖ + 2 →
        Quadratic.bottcher_map c z ∉ ((↑) '' K : Set ℂ)) :
    IsClosed
      ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
        Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) := by
  let C : Set ℂ := {z : ℂ | ‖c‖ + 2 ≤ ‖z‖}
  have hCclosed : IsClosed C := by
    simpa [C] using (isClosed_le continuous_const continuous_norm)
  have hcontOnC : ContinuousOn (Quadratic.bottcher_map c) C := by
    intro z hzC
    have hpos : 0 < ‖c‖ + 2 := by
      nlinarith [norm_nonneg c]
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hpos hzC
    have hzne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
    exact (bottcher_map_continuousAt_of_ne_zero_outsidePlan c z hzne).continuousWithinAt
  let g : C → ℂ := fun z => Quadratic.bottcher_map c z.1
  have hgcont : Continuous g := by
    exact (continuousOn_iff_continuous_restrict).1 hcontOnC
  have hImgClosed : IsClosed (((↑) '' K : Set ℂ)) := (hK.image continuous_subtype_val).isClosed
  have hpreClosedSub : IsClosed (g ⁻¹' (((↑) '' K : Set ℂ))) := hImgClosed.preimage hgcont
  have hValClosedMap : IsClosedMap (Subtype.val : C → ℂ) :=
    (Topology.IsClosedEmbedding.subtypeVal hCclosed).isClosedMap
  have hclosed_ge :
      IsClosed
        ((Subtype.val) '' (g ⁻¹' (((↑) '' K : Set ℂ))) : Set ℂ) :=
    hValClosedMap _ hpreClosedSub
  have hclosed_ge_eq :
      ((Subtype.val) '' (g ⁻¹' (((↑) '' K : Set ℂ))) : Set ℂ) =
        ({z : ℂ | ‖c‖ + 2 ≤ ‖z‖ ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · intro hz
      refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
      exact hz.2
  have hset_eq :
      ({z : ℂ | ‖z‖ > ‖c‖ + 2 ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) =
        ({z : ℂ | ‖c‖ + 2 ≤ ‖z‖ ∧
          Quadratic.bottcher_map c z ∈ ((↑) '' K : Set ℂ)} : Set ℂ) := by
    ext z
    constructor
    · intro hz
      exact ⟨le_of_lt hz.1, hz.2⟩
    · intro hz
      rcases hz with ⟨hzge, hzK⟩
      rcases lt_or_eq_of_le hzge with hlt | heq
      · exact ⟨hlt, hzK⟩
      · exfalso
        exact (hboundary z heq.symm) hzK
  rw [hset_eq]
  rw [← hclosed_ge_eq]
  exact hclosed_ge

/-- Properness of the restricted outside-open map from outside-open analyticity
plus boundary exclusion on compact exterior targets. -/
lemma isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_boundary_exclusion
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (hboundary :
      ∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
        ∀ z, ‖z‖ = ‖c‖ + 2 →
          Quadratic.bottcher_map c z ∉ ((↑) '' K : Set ℂ)) :
    IsProperMap (bottcher_map_outside_open_to_exterior c) :=
  isProperMap_bottcher_map_outside_open_to_exterior_of_analyticAt_of_preimage_closed c
    hanalytic (fun K hK =>
      isClosed_outside_open_preimage_image_compact_of_boundary_exclusion c K hK
        (hboundary K hK))

/-- At `c = 2`, the boundary-exclusion family cannot hold for all compact
exterior targets: the singleton containing the image of one boundary point is a
compact counterexample. -/
lemma exists_compact_exterior_set_violating_boundary_exclusion_two :
    ∃ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K ∧
      ¬ (∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
        Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) := by
  let z0 : ℂ := ((‖(2 : ℂ)‖ + 2 : ℝ) : ℂ)
  have hnonneg : 0 ≤ ‖(2 : ℂ)‖ + 2 := by
    nlinarith [norm_nonneg (2 : ℂ)]
  have hz0_eq_abs : ‖z0‖ = |‖(2 : ℂ)‖ + 2| := by
    simpa [z0] using (Complex.norm_real (‖(2 : ℂ)‖ + 2))
  have hz0_eq : ‖z0‖ = ‖(2 : ℂ)‖ + 2 := by
    exact hz0_eq_abs.trans (abs_of_nonneg hnonneg)
  have hz0_ge : ‖z0‖ ≥ ‖(2 : ℂ)‖ + 2 := by
    linarith [hz0_eq]
  have hz0_out : z0 ∈ outside_disk (2 : ℂ) :=
    large_norm_mem_outside_disk (2 : ℂ) z0 hz0_ge
  have hw0_ext : 1 < ‖Quadratic.bottcher_map (2 : ℂ) z0‖ :=
    bottcher_map_norm_gt_one_of_outside (2 : ℂ) hz0_out
  let w0 : {w : ℂ // 1 < ‖w‖} := ⟨Quadratic.bottcher_map (2 : ℂ) z0, hw0_ext⟩
  refine ⟨({w0} : Set {w : ℂ // 1 < ‖w‖}), isCompact_singleton, ?_⟩
  intro hboundary
  have hnot :
      Quadratic.bottcher_map (2 : ℂ) z0 ∉
        ((↑) '' ({w0} : Set {w : ℂ // 1 < ‖w‖}) : Set ℂ) :=
    hboundary z0 hz0_eq
  have hmem :
      Quadratic.bottcher_map (2 : ℂ) z0 ∈
        ((↑) '' ({w0} : Set {w : ℂ // 1 < ‖w‖}) : Set ℂ) := by
    refine ⟨w0, by simp, rfl⟩
  exact hnot hmem

/-- Therefore the universal boundary-exclusion family at `c = 2` is false. -/
lemma not_boundary_exclusion_family_two :
    ¬ (∀ K : Set {w : ℂ // 1 < ‖w‖}, IsCompact K →
      ∀ z, ‖z‖ = ‖(2 : ℂ)‖ + 2 →
        Quadratic.bottcher_map (2 : ℂ) z ∉ ((↑) '' K : Set ℂ)) := by
  intro hboundary
  rcases exists_compact_exterior_set_violating_boundary_exclusion_two with ⟨K, hK, hnot⟩
  exact hnot (hboundary K hK)

/-- Closed range of the restricted outside-open Böttcher map from properness of
the restricted map itself. -/
lemma isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap
    (c : ℂ)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior c)) :
    IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)) := by
  have hClosedMap : IsClosedMap (bottcher_map_outside_open_to_exterior c) :=
    hproper.isClosedMap
  simpa [Set.image_univ] using (hClosedMap Set.univ isClosed_univ)

/-- Outside-open surjectivity on the exterior from a clopen argument on the
restricted map `outside_open → exterior`. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_of_isLocalHomeomorph_restrict
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior c)) :
    BottcherSurjOnExteriorFromOutsideOpen c := by
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  let E : Set ℂ := {w : ℂ | 1 < ‖w‖}
  let f : U → E := bottcher_map_outside_open_to_exterior c
  have hRopen : IsOpen (Set.range f) := by
    simpa [Set.image_univ] using (hlocal.isOpenMap Set.univ isOpen_univ)
  have hRclosed : IsClosed (Set.range f) := hclosed
  have hRnonempty : (Set.range f).Nonempty := by
    let z0 : ℂ := ((‖c‖ + 3 : ℝ) : ℂ)
    have hz0 : z0 ∈ U := by
      have hnonneg : 0 ≤ ‖c‖ + 3 := by
        have hc : 0 ≤ ‖c‖ := norm_nonneg c
        nlinarith
      have hgt : ‖c‖ + 2 < ‖c‖ + 3 := by linarith
      have hnorm_eq : ‖((‖c‖ + 3 : ℝ) : ℂ)‖ = ‖c‖ + 3 := by
        simpa [abs_of_nonneg hnonneg] using (Complex.norm_real (‖c‖ + 3))
      have hnorm : ‖((‖c‖ + 3 : ℝ) : ℂ)‖ > ‖c‖ + 2 := by
        linarith [hgt, hnorm_eq]
      simpa [z0, U] using hnorm
    exact ⟨f ⟨z0, hz0⟩, ⟨⟨z0, hz0⟩, rfl⟩⟩
  letI : ConnectedSpace E :=
    (isConnected_iff_connectedSpace).1 isConnected_exterior
  have hRuniv : Set.range f = Set.univ :=
    IsClopen.eq_univ ⟨hRclosed, hRopen⟩ hRnonempty
  intro w hw
  have hwR : (⟨w, hw⟩ : E) ∈ Set.range f := by
    simp [hRuniv]
  rcases hwR with ⟨z, hz⟩
  refine ⟨z.1, z.2, ?_⟩
  exact congrArg Subtype.val hz

/-- `c = 2` specialization: outside-open surjectivity on the exterior from
closed range of the restricted map plus restricted local-homeomorph payload. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hlocal : IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_of_isLocalHomeomorph_restrict
    (2 : ℂ) hclosed hlocal

/-- Convert local-homeomorph on an open set into local-homeomorph of the
restricted function on the subtype domain. -/
lemma isLocalHomeomorph_restrict_of_isLocalHomeomorphOn_open
    {f : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s)
    (hlocal : IsLocalHomeomorphOn f s) :
    IsLocalHomeomorph (s.restrict f) := by
  intro x
  rcases hlocal x x.2 with ⟨e, hx, hfe⟩
  let S : TopologicalSpace.Opens ℂ := ⟨s, hs⟩
  have hS : Nonempty S := ⟨⟨x.1, x.2⟩⟩
  refine ⟨e.subtypeRestr hS, ?_, ?_⟩
  · simpa [S] using hx
  · funext y
    change f y.1 = e y.1
    simp [hfe]

/-- Codomain restriction preserves local-homeomorph when all values land in the
target subset. -/
lemma isLocalHomeomorph_codRestrict_of_isLocalHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y}
    (hlocal : IsLocalHomeomorph f)
    (hs : ∀ x, f x ∈ s) :
    IsLocalHomeomorph (codRestrict f s hs) := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict] at hlocal ⊢
  intro x
  rcases hlocal x with ⟨U, hU, hEmb⟩
  refine ⟨U, hU, ?_⟩
  let g : U → s :=
    codRestrict (U.restrict f) s (by
      intro z
      exact hs z.1)
  have hgcont : Continuous g := by
    exact (hEmb.toIsEmbedding.continuous.codRestrict (by
      intro z
      exact hs z.1))
  have hginj : Function.Injective g := by
    intro a b hab
    exact hEmb.toIsEmbedding.injective (congrArg Subtype.val hab)
  have hgopen : IsOpenMap g := by
    simpa [g, Set.restrict] using
      (IsOpenMap.codRestrict hEmb.isOpenMap (by
        intro z
        exact hs z.1))
  have hEmb' : IsOpenEmbedding g :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hgcont hginj hgopen
  simpa [g, Set.restrict] using hEmb'

/-- Restricted-map local-homeomorph from local-homeomorph on outside-open. -/
lemma isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_isLocalHomeomorphOn_outside_open
    (c : ℂ)
    (hlocal : IsLocalHomeomorphOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior c) := by
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  let E : Set ℂ := {w : ℂ | 1 < ‖w‖}
  have hUopen : IsOpen U := by
    simpa [U] using (isOpen_lt continuous_const continuous_norm)
  have hlocalU : IsLocalHomeomorph (U.restrict (Quadratic.bottcher_map c)) := by
    exact isLocalHomeomorph_restrict_of_isLocalHomeomorphOn_open hUopen (by simpa [U] using hlocal)
  have hs : ∀ z : U, (U.restrict (Quadratic.bottcher_map c)) z ∈ E := by
    intro z
    have hzU : z.1 ∈ ({w : ℂ | ‖w‖ > ‖c‖ + 2} : Set ℂ) := by
      change z.1 ∈ U
      exact z.2
    exact bottcher_map_norm_gt_one_of_outside c
      (outside_open_subset_outside_disk c hzU)
  simpa [bottcher_map_outside_open_to_exterior, U, E, Set.restrict] using
    isLocalHomeomorph_codRestrict_of_isLocalHomeomorph (f := U.restrict (Quadratic.bottcher_map c))
      (s := E) hlocalU hs

/-- Build restricted-map local-homeomorph from local analyticity plus
derivative nonvanishing on outside-open. -/
lemma isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_analyticAt_of_deriv_ne_zero
    (c : ℂ)
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (hderiv : ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0) :
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior c) := by
  exact isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_isLocalHomeomorphOn_outside_open c
    (bottcher_map_isLocalHomeomorphOn_outside_open_of_analyticAt_of_deriv_ne_zero
      c hanalytic hderiv)

/-- Outside-open surjectivity from closed range of the restricted map plus
local analyticity and derivative nonvanishing on outside-open. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (hderiv : ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0) :
    BottcherSurjOnExteriorFromOutsideOpen c := by
  exact bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_of_isLocalHomeomorph_restrict c
    hclosed
    (isLocalHomeomorph_bottcher_map_outside_open_to_exterior_of_analyticAt_of_deriv_ne_zero
      c hanalytic hderiv)

/-- `c = 2` specialization: outside-open surjectivity from closed range of the
restricted map plus local analyticity and derivative nonvanishing on outside-open. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (hderiv : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → deriv (Quadratic.bottcher_map (2 : ℂ)) z ≠ 0) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
    (2 : ℂ) hclosed hanalytic hderiv

/-- Construct external-ray data from outside-open injectivity + exterior
    surjectivity by outside-open preimages. -/
theorem external_ray_map_data_of_injOn_outside_open_of_surj_exterior
    (c : ℂ)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2})
    (h_surj : BottcherSurjOnExteriorFromOutsideOpen c) :
    Quadratic.ExternalRayMapData c := by
  classical
  let f : ℂ → ℂ := fun w =>
    if hw : 1 < ‖w‖ then Classical.choose (h_surj w hw) else 0
  refine ⟨f, ?_, ?_⟩
  · intro w hw
    have hspec : Quadratic.bottcher_map c (Classical.choose (h_surj w hw)) = w :=
      (Classical.choose_spec (h_surj w hw)).2
    simpa [f, hw] using hspec
  · intro z hz
    have hz_out : z ∈ ({z : ℂ | ‖z‖ > ‖c‖ + 2} : Set ℂ) := hz
    have hz_disk : z ∈ outside_disk c := outside_open_subset_outside_disk c hz_out
    have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
      outside_disk_subset_quadratic_basin c hz_disk
    have hpos : 0 < MLC.Quadratic.green_function c z :=
      green_function_pos_of_basin c z hz_basin
    have hnorm : 1 < ‖Quadratic.bottcher_map c z‖ :=
      bottcher_map_norm_gt_one_of_basin c z hz_basin hpos
    have hspec := Classical.choose_spec (h_surj (Quadratic.bottcher_map c z) hnorm)
    have hz_choose :
        Classical.choose (h_surj (Quadratic.bottcher_map c z) hnorm) = z := by
      apply h_inj hspec.1 hz_out
      simpa using hspec.2
    simp [f, hnorm, hz_choose]

/-- Construct external-ray data from closed range on the restricted map plus
local analyticity and outside-open injectivity. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Quadratic.ExternalRayMapData c := by
  exact external_ray_map_data_of_injOn_outside_open_of_surj_exterior c h_inj
    (bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
      c hclosed hanalytic
      (bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn
        c hanalytic h_inj))

/-- Construct external-ray data from closed range plus the outside-open
analyticity seam payload and outside-open injectivity. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open
    c hclosed hanalytic h_inj

/-- Construct external-ray data from closed range plus the outside-open local
analytic-chart seam payload and outside-open injectivity. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_chart : ∀ z, ‖z‖ > ‖c‖ + 2 →
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ AnalyticOnNhd ℂ (Quadratic.bottcher_map c) U)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Quadratic.ExternalRayMapData c := by
  have hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z := by
    intro z hz
    rcases h_chart z hz with ⟨U, _hUopen, hzU, hUanalytic⟩
    exact hUanalytic z hzU
  exact external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open
    c hclosed hanalytic h_inj

lemma bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed_of_left_inverse_on_outside_open
    (c : ℂ)
    (hproper : IsProperMap (Quadratic.bottcher_map c))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map c))
    (h_left : BottcherLeftInverseOnOutsideOpenData c)
    {y : ℂ}
    (hyimg : y ∈ Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2})
    (hfiberU :
      ({z : ℂ | Quadratic.bottcher_map c z = y} : Set ℂ) ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  exact bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed c hproper hlocal
    (bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open c h_left) hyimg hfiberU

lemma exists_bottcher_outside_seed_of_continuous
    (c : ℂ) (hcont : Continuous (Quadratic.bottcher_map c)) :
    ∃ y, y ∈ Quadratic.bottcher_map c '' {z : ℂ | ‖z‖ > ‖c‖ + 2} ∧
      ({z : ℂ | Quadratic.bottcher_map c z = y} : Set ℂ) ⊆ {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ ‖c‖ + 2}
  have hKcompact : IsCompact K := by
    have hK :
        K = Metric.closedBall (0 : ℂ) (‖c‖ + 2) := by
      ext z
      simp [K, Metric.mem_closedBall, dist_eq_norm]
    rw [hK]
    exact isCompact_closedBall (0 : ℂ) (‖c‖ + 2)
  have himageKcompact : IsCompact (Quadratic.bottcher_map c '' K) :=
    hKcompact.image hcont
  rcases himageKcompact.isBounded.subset_closedBall (0 : ℂ) with ⟨B, hBsubset⟩
  rcases exists_norm_bottcher_map_gt_of_large_norm c B with ⟨S, hS⟩
  let R : ℝ := max S (‖c‖ + 3)
  let z0 : ℂ := (R : ℂ)
  have hRnonneg : 0 ≤ R := by
    have hc : 0 ≤ ‖c‖ + 3 := by nlinarith [norm_nonneg c]
    exact le_trans hc (le_max_right _ _)
  have hz0norm : ‖z0‖ = R := by
    simp [z0, Real.norm_eq_abs, abs_of_nonneg hRnonneg]
  have hz0S : S ≤ ‖z0‖ := by
    calc
      S ≤ R := le_max_left _ _
      _ = ‖z0‖ := hz0norm.symm
  have hygt : B < ‖Quadratic.bottcher_map c z0‖ := hS z0 hz0S
  have hz0U : z0 ∈ {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
    have hRge : ‖c‖ + 3 ≤ R := le_max_right _ _
    have : ‖c‖ + 2 < R := by linarith
    simpa [hz0norm]
  let y : ℂ := Quadratic.bottcher_map c z0
  refine ⟨y, ?_, ?_⟩
  · exact ⟨z0, hz0U, rfl⟩
  · intro x hx
    by_contra hxU
    have hxK : x ∈ K := by
      have hxle : ‖x‖ ≤ ‖c‖ + 2 := by
        exact le_of_not_gt (by
          intro hgt
          exact hxU (by simpa using hgt))
      exact hxle
    have hyK : y ∈ Quadratic.bottcher_map c '' K := by
      refine ⟨x, hxK, ?_⟩
      simpa [y] using hx
    have hyB : ‖y‖ ≤ B := by
      have : y ∈ Metric.closedBall (0 : ℂ) B := hBsubset hyK
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    have hygt' : B < ‖y‖ := by simpa [y] using hygt
    exact (not_lt_of_ge hyB) hygt'

lemma bottcher_map_inj_on_basin_of_proper_localHomeomorph_of_left_inverse_on_outside_open
    (c : ℂ)
    (hproper : IsProperMap (Quadratic.bottcher_map c))
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map c))
    (h_left : BottcherLeftInverseOnOutsideOpenData c) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  rcases exists_bottcher_outside_seed_of_continuous c hlocal.continuous with ⟨y, hyimg, hfiberU⟩
  exact bottcher_map_inj_on_basin_of_proper_localHomeomorph_and_outside_seed_of_left_inverse_on_outside_open
    c hproper hlocal h_left hyimg hfiberU

lemma bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin_of_injOn_outside_open_of_exterior_subset_image_basin
    (c : ℂ)
    (hproper : IsProperMap (Quadratic.bottcher_map c))
    (hlocal : IsLocalHomeomorphOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c))
    (hUinj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2})
    (hsub :
      {w : ℂ | 1 < ‖w‖} ⊆
        (Quadratic.bottcher_map c '' Quadratic.basin_of_infinity c)) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  let f : ℂ → ℂ := Quadratic.bottcher_map c
  let s : Set ℂ := Quadratic.basin_of_infinity c
  have hsopen : IsOpen s := basin_of_infinity_isOpen c
  have hfiberS : ∀ y, y ∈ f '' s → ({x : ℂ | f x = y} : Set ℂ) ⊆ s := by
    intro y hyimg x hx
    have hygt : 1 < ‖y‖ := by
      rcases hyimg with ⟨z, hz, rfl⟩
      exact bottcher_map_norm_gt_one_of_basin c z hz (green_function_pos_of_basin c z hz)
    have hxy : f x = y := by
      simpa using hx
    have hxgt : 1 < ‖f x‖ := by
      calc
        1 < ‖y‖ := hygt
        _ = ‖f x‖ := by simp [hxy]
    exact bottcher_map_norm_gt_one_implies_basin c (z := x) hxgt
  have himage_eq : f '' s = {w : ℂ | 1 < ‖w‖} := by
    refine subset_antisymm ?_ ?_
    · intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      exact bottcher_map_norm_gt_one_of_basin c z hz (green_function_pos_of_basin c z hz)
    · exact hsub
  have hconn : IsConnected (f '' s) := by
    simpa [himage_eq] using isConnected_exterior
  have hdeg1 : ∃ y : f '' s, Nat.card ({x : ℂ // f x = y.1}) = 1 := by
    rcases exists_bottcher_outside_seed_of_continuous c hproper.continuous with
      ⟨y, hyimg, hfiberU⟩
    have hcard1 : Nat.card ({x : ℂ // f x = y}) = 1 :=
      natCard_fiber_eq_one_of_injOn_of_mem_image_of_fiber_subset
        (f := f) (U := {z : ℂ | ‖z‖ > ‖c‖ + 2}) (y := y)
        hUinj hyimg hfiberU
    have hyimgBasin : y ∈ f '' s := by
      rcases hyimg with ⟨z, hz, rfl⟩
      refine ⟨z, ?_, rfl⟩
      exact outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz)
    exact ⟨⟨y, hyimgBasin⟩, hcard1⟩
  simpa [f, s] using
    (injOn_of_isProperMap_isLocalHomeomorphOn_of_open_of_fiber_subset_on_image_of_connected_image
      (f := f) (s := s) hproper hlocal hsopen hconn hfiberS hdeg1)

/-- Exterior inclusion in the basin image from a right-inverse-on-exterior
    payload. -/
lemma exterior_subset_image_basin_of_right_inverse
    (c : ℂ)
    (h_right : BottcherRightInverseOnExteriorDataOutsidePlan c) :
    {w : ℂ | 1 < ‖w‖} ⊆
      (Quadratic.bottcher_map c '' Quadratic.basin_of_infinity c) := by
  intro w hw
  rcases h_right with ⟨f, hf⟩
  have hfw : Quadratic.bottcher_map c (f w) = w := hf w hw
  have hbasin : f w ∈ Quadratic.basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := f w)
      (by simpa [hfw] using hw)
  exact ⟨f w, hbasin, hfw⟩

/-- Basin injectivity from `IsLocalHomeomorphOn` via explicit outside-open left-
    inverse and exterior right-inverse seam data. -/
lemma bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin_of_left_inverse_on_outside_open_of_right_inverse_on_exterior
    (c : ℂ)
    (hproper : IsProperMap (Quadratic.bottcher_map c))
    (hlocal : IsLocalHomeomorphOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c))
    (h_left : BottcherLeftInverseOnOutsideOpenData c)
    (h_right : BottcherRightInverseOnExteriorDataOutsidePlan c) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  exact bottcher_map_inj_on_basin_of_proper_localHomeomorphOn_basin_of_injOn_outside_open_of_exterior_subset_image_basin
    c hproper hlocal
    (bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open c h_left)
    (exterior_subset_image_basin_of_right_inverse c h_right)

lemma bottcher_map_inj_on_basin_of_isLocalHomeomorph_of_left_inverse_on_outside_open
    (c : ℂ)
    (hlocal : IsLocalHomeomorph (Quadratic.bottcher_map c))
    (h_left : BottcherLeftInverseOnOutsideOpenData c) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  have hproper : IsProperMap (Quadratic.bottcher_map c) :=
    bottcher_map_isProperMap_of_continuous c hlocal.continuous
  exact bottcher_map_inj_on_basin_of_proper_localHomeomorph_of_left_inverse_on_outside_open
    c hproper hlocal h_left

theorem bottcher_map_inj_on_outside_of_slit
    (c : ℂ)
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c →
      w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Set.InjOn (Quadratic.bottcher_map c) (outside_disk c) := by
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  have h_left : ∀ z, z ∈ U →
      Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z := by
    intro z hz
    exact bottcher_left_inv_outside_open_of_local c z (by simpa [U] using hz)
  have h_maps : MapsTo (quadratic_map c) U U := by
    simpa [U] using (quadratic_map_maps_outside_open c)
  have h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ U := by
    intro z hz
    simpa [U] using (basin_escape_outside_open c z hz)
  have h_inj_basin :
      Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) :=
    bottcher_map_inj_on_basin_of_left_inv c U h_left h_maps h_escape
      (bottcher_conj_iter c) h_iter_eq_imp
  simpa [outside_disk] using h_inj_basin

theorem bottcher_map_inj_on_outside_of_slit_of_iter_left_inverse
    (c : ℂ) (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    Set.InjOn (Quadratic.bottcher_map c) (outside_disk c) := by
  have h_iter_eq_imp :=
    quadratic_map_iter_eq_imp_eq_of_iter_left_inverse c h_left_iter
  exact bottcher_map_inj_on_outside_of_slit c h_iter_eq_imp

/-- Outside-open injectivity from the iterate-left-inverse hypothesis on the
basin. -/
theorem bottcher_map_inj_on_outside_open_of_iter_left_inverse
    (c : ℂ) (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  exact
    (bottcher_map_inj_on_outside_of_slit_of_iter_left_inverse c h_left_iter).mono
      (outside_open_subset_outside_disk c)

/-- Closed-range restricted-map surjectivity from local analyticity on
outside-open plus the iterate-left-inverse injectivity route. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    BottcherSurjOnExteriorFromOutsideOpen c := by
  exact bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
    c hclosed hanalytic
    (bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn c hanalytic
      (bottcher_map_inj_on_outside_open_of_iter_left_inverse c h_left_iter))

/-- Construct external-ray data from closed range plus local analyticity and the
iterate-left-inverse injectivity route. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hanalytic : ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    Quadratic.ExternalRayMapData c := by
  exact external_ray_map_data_of_injOn_outside_open_of_surj_exterior c
    (bottcher_map_inj_on_outside_open_of_iter_left_inverse c h_left_iter)
    (bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
      c hclosed hanalytic h_left_iter)

/-- `c = 2` specialization of the iterate-left-inverse external-ray-data bridge. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hanalytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_iter_left_inverse
    (2 : ℂ) hclosed hanalytic h_left_iter

-- The open exterior `{‖z‖ > ‖c‖ + 2}` is the natural domain for Step 1.
-- Extending analyticity to the closed `outside_disk` would need boundary control.

def slitPlaneRot (θ : ℝ) : Set ℂ :=
  {z | z * Complex.exp (-Complex.I * θ) ∈ Complex.slitPlane}

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

lemma exists_open_subset_slit_orbit_basin_of_mem_nhds
    (c z₀ : ℂ)
    (hslit : slit_orbit c ∈ 𝓝 z₀)
    (hbasin : Quadratic.basin_of_infinity c ∈ 𝓝 z₀) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ slit_orbit c ∩ Quadratic.basin_of_infinity c := by
  rcases Metric.mem_nhds_iff.mp hslit with ⟨ε1, ε1pos, hε1⟩
  rcases Metric.mem_nhds_iff.mp hbasin with ⟨ε2, ε2pos, hε2⟩
  let ε := min ε1 ε2
  let U : Set ℂ := {z : ℂ | dist z z₀ < ε}
  have hUopen : IsOpen U := by
    simpa [U, Metric.ball, Set.mem_setOf_eq] using
      (Metric.isOpen_ball : IsOpen (Metric.ball z₀ ε))
  have hz₀U : z₀ ∈ U := by
    have hεpos : 0 < ε := lt_min ε1pos ε2pos
    simpa [U, dist_self] using hεpos
  have hUsub : U ⊆ slit_orbit c ∩ Quadratic.basin_of_infinity c := by
    intro z hz
    have hz1 : dist z z₀ < ε1 := lt_of_lt_of_le hz (min_le_left _ _)
    have hz2 : dist z z₀ < ε2 := lt_of_lt_of_le hz (min_le_right _ _)
    exact ⟨hε1 hz1, hε2 hz2⟩
  exact ⟨U, hUopen, hz₀U, hUsub⟩

lemma bottcher_map_analyticAt_of_mem_nhds_slit_basin
    (c z₀ : ℂ)
    (hslit : slit_orbit c ∈ 𝓝 z₀)
    (hbasin : Quadratic.basin_of_infinity c ∈ 𝓝 z₀) :
    AnalyticAt ℂ (Quadratic.bottcher_map c) z₀ := by
  rcases exists_open_subset_slit_orbit_basin_of_mem_nhds c z₀ hslit hbasin with
    ⟨U, hUopen, hz₀U, hUsub⟩
  have hUslit : U ⊆ slit_orbit c := fun z hz => (hUsub hz).1
  have hUbasin : U ⊆ Quadratic.basin_of_infinity c := fun z hz => (hUsub hz).2
  exact bottcher_map_analyticAt_of_open c U hUopen hUslit hUbasin hz₀U

/-- Local analyticity payload on outside-open derived from neighborhood-level
slit membership plus basin openness. -/
lemma bottcher_map_analyticAt_on_outside_open_of_mem_nhds_slit
    (c : ℂ)
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z := by
  intro z hz
  have hz_out : z ∈ {w : ℂ | ‖w‖ > ‖c‖ + 2} := by simpa using hz
  have hz_disk : z ∈ outside_disk c := outside_open_subset_outside_disk c hz_out
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c hz_disk
  exact bottcher_map_analyticAt_of_mem_nhds_slit_basin c z
    (hslit_nhds z hz)
    ((basin_of_infinity_isOpen c).mem_nhds hz_basin)

/-- Framework seam: outside-open analyticity payload for `bottcher_map`. -/
def OutsideOpenAnalyticityHypothesis (c : ℂ) : Prop :=
  ∀ z, ‖z‖ > ‖c‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map c) z

/-- Outside-open analyticity payload for the quotient map
`z ↦ bottcher_map c z / z`. -/
def OutsideOpenQuotientAnalyticityHypothesis (c : ℂ) : Prop :=
  ∀ z, ‖z‖ > ‖c‖ + 2 →
    AnalyticAt ℂ (fun w : ℂ => Quadratic.bottcher_map c w / w) z

/-- Outside-open real-scale quotient payload:
`bottcher_map c z / z` is a positive real scalar at each outside-open point. -/
def OutsideOpenQuotientRealScaleHypothesis (c : ℂ) : Prop :=
  ∀ z, ‖z‖ > ‖c‖ + 2 →
    ∃ r : ℝ, 0 < r ∧ Quadratic.bottcher_map c z / z = (r : ℂ)

/-- Combined quotient payload used for non-slit rigidity attempts. -/
def OutsideOpenQuotientAnalyticRealScalePayload (c : ℂ) : Prop :=
  OutsideOpenQuotientAnalyticityHypothesis c ∧
    OutsideOpenQuotientRealScaleHypothesis c

/-- Framework seam: outside-open analyticity+injectivity payload for
`bottcher_map` (non-slit route target shape). -/
def OutsideOpenAnalyticInjPayload (c : ℂ) : Prop :=
  OutsideOpenAnalyticityHypothesis c ∧
    Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}

/-- `c = 2` specialization of the outside-open analyticity+injectivity seam. -/
def OutsideOpenAnalyticInjNonSlitPayloadTwo : Prop :=
  OutsideOpenAnalyticInjPayload (2 : ℂ)

/-- `c = 2` specialization of the quotient analyticity seam. -/
def OutsideOpenQuotientAnalyticityHypothesisTwo : Prop :=
  OutsideOpenQuotientAnalyticityHypothesis (2 : ℂ)

/-- `c = 2` specialization of the quotient analytic+real-scale seam. -/
def OutsideOpenQuotientAnalyticRealScalePayloadTwo : Prop :=
  OutsideOpenQuotientAnalyticRealScalePayload (2 : ℂ)

/-- Quotient-constancy seam: the outside-open quotient
`z ↦ bottcher_map c z / z` is globally constant. -/
def OutsideOpenQuotientConstHypothesis (c : ℂ) : Prop :=
  ∃ q : ℂ, ∀ z, ‖z‖ > ‖c‖ + 2 → Quadratic.bottcher_map c z / z = q

/-- `c = 2` specialization of quotient constancy. -/
def OutsideOpenQuotientConstHypothesisTwo : Prop :=
  OutsideOpenQuotientConstHypothesis (2 : ℂ)

/-- Strong quotient-rigidity witness: on outside-open, `bottcher_map c` is a
positive-real scalar multiple of the identity map. -/
def OutsideOpenQuotientConstRealWitness (c : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    ∀ z, ‖z‖ > ‖c‖ + 2 → Quadratic.bottcher_map c z = (r : ℂ) * z

/-- `c = 2` specialization of the strong quotient-rigidity witness. -/
def OutsideOpenQuotientConstRealWitnessTwo : Prop :=
  OutsideOpenQuotientConstRealWitness (2 : ℂ)

/-- Framework seam: for each outside-open point, provide a local open chart on
which `bottcher_map` is analytic. -/
def OutsideOpenLocalAnalyticChartHypothesis (c : ℂ) : Prop :=
  ∀ z, ‖z‖ > ‖c‖ + 2 →
    ∃ U : Set ℂ,
      IsOpen U ∧ z ∈ U ∧ AnalyticOnNhd ℂ (Quadratic.bottcher_map c) U

/-- Stronger framework seam: local analytic charts that stay inside
outside-open. -/
def OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (c : ℂ) : Prop :=
  ∀ z, ‖z‖ > ‖c‖ + 2 →
    ∃ U : Set ℂ,
      IsOpen U ∧ z ∈ U ∧
        U ⊆ {w : ℂ | ‖w‖ > ‖c‖ + 2} ∧
        AnalyticOnNhd ℂ (Quadratic.bottcher_map c) U

/-- Forget the subset side condition on outside-open local analytic charts. -/
lemma outsideOpenLocalAnalyticChartHypothesis_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    (c : ℂ)
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis c) :
    OutsideOpenLocalAnalyticChartHypothesis c := by
  intro z hz
  rcases h_chart z hz with ⟨U, hUopen, hzU, _hUsub, hUanalytic⟩
  exact ⟨U, hUopen, hzU, hUanalytic⟩

/-- A local analytic chart payload implies the outside-open `AnalyticAt`
hypothesis. -/
lemma outsideOpenAnalyticityHypothesis_of_outsideOpenLocalAnalyticChartHypothesis
    (c : ℂ)
    (h_chart : OutsideOpenLocalAnalyticChartHypothesis c) :
    OutsideOpenAnalyticityHypothesis c := by
  intro z hz
  rcases h_chart z hz with ⟨U, _hUopen, hzU, hUanalytic⟩
  exact hUanalytic z hzU

/-- Project analyticity from the combined outside-open analytic/injective seam. -/
lemma outsideOpenAnalyticityHypothesis_of_outsideOpenAnalyticInjPayload
    (c : ℂ)
    (h_payload : OutsideOpenAnalyticInjPayload c) :
    OutsideOpenAnalyticityHypothesis c :=
  h_payload.1

/-- Project outside-open injectivity from the combined analytic/injective seam. -/
lemma injOn_outside_open_of_outsideOpenAnalyticInjPayload
    (c : ℂ)
    (h_payload : OutsideOpenAnalyticInjPayload c) :
    Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
  h_payload.2

/-- Outside-open analyticity of `bottcher_map` induces outside-open analyticity
of the quotient map `z ↦ bottcher_map c z / z`. -/
lemma outsideOpenQuotientAnalyticityHypothesis_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    OutsideOpenQuotientAnalyticityHypothesis c := by
  intro z hz
  have hz_norm_pos : 0 < ‖z‖ := by
    linarith [hz, norm_nonneg c]
  have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz_norm_pos)
  exact (h_analytic z hz).div analyticAt_id hz_ne

/-- Outside-open analyticity of the quotient map `z ↦ bottcher_map c z / z`
implies outside-open analyticity of `bottcher_map c`. -/
lemma outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientAnalyticityHypothesis
    (c : ℂ)
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesis c) :
    OutsideOpenAnalyticityHypothesis c := by
  intro z hz
  have hz_norm_pos : 0 < ‖z‖ := by
    linarith [hz, norm_nonneg c]
  have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz_norm_pos)
  have hmul : AnalyticAt ℂ (fun w : ℂ => w * (Quadratic.bottcher_map c w / w)) z := by
    exact analyticAt_id.mul (h_qanalytic z hz)
  have hEq :
      (fun w : ℂ => w * (Quadratic.bottcher_map c w / w)) =ᶠ[𝓝 z]
        (Quadratic.bottcher_map c) := by
    have hne : {w : ℂ | w ≠ 0} ∈ 𝓝 z := by
      exact IsOpen.mem_nhds isOpen_ne hz_ne
    exact Filter.mem_of_superset hne (by
      intro w hw
      have hw0 : w ≠ 0 := by simpa using hw
      change w * (Quadratic.bottcher_map c w / w) = Quadratic.bottcher_map c w
      calc
        w * (Quadratic.bottcher_map c w / w)
            = w * (w⁻¹ * Quadratic.bottcher_map c w) := by
                simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        _ = (w * w⁻¹) * Quadratic.bottcher_map c w := by ac_rfl
        _ = Quadratic.bottcher_map c w := by simp [hw0])
  exact hmul.congr hEq

/-- The outside-open real-scale quotient payload holds unconditionally from the
explicit `bottcher_map` quotient form. -/
lemma outsideOpenQuotientRealScaleHypothesis_of_bottcher_map_div
    (c : ℂ) :
    OutsideOpenQuotientRealScaleHypothesis c := by
  intro z hz
  exact bottcher_map_div_eq_real_scale_of_outside_open c z hz

/-- Any outside-open analytic/injective payload yields the quotient
analytic+real-scale payload used by the non-slit rigidity route. -/
lemma outsideOpenQuotientAnalyticRealScalePayload_of_outsideOpenAnalyticInjPayload
    (c : ℂ)
    (h_payload : OutsideOpenAnalyticInjPayload c) :
    OutsideOpenQuotientAnalyticRealScalePayload c := by
  refine ⟨?_, outsideOpenQuotientRealScaleHypothesis_of_bottcher_map_div c⟩
  exact outsideOpenQuotientAnalyticityHypothesis_of_outsideOpenAnalyticityHypothesis c
    (outsideOpenAnalyticityHypothesis_of_outsideOpenAnalyticInjPayload c h_payload)

/-- `c = 2` specialization: non-slit analytic/injective payload yields quotient
analytic+real-scale payload. -/
lemma outsideOpenQuotientAnalyticRealScalePayloadTwo_of_nonSlitPayload
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    OutsideOpenQuotientAnalyticRealScalePayloadTwo :=
  outsideOpenQuotientAnalyticRealScalePayload_of_outsideOpenAnalyticInjPayload
    (2 : ℂ) h_payload

/-- The outside-open set `{‖z‖ > ‖c‖ + 2}` is preconnected. -/
lemma isPreconnected_outside_open (c : ℂ) :
    IsPreconnected {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  let R : ℝ := ‖c‖ + 2
  let E : Set ℂ := {w : ℂ | 1 < ‖w‖}
  let f : ℂ → ℂ := fun w => ((R : ℝ) : ℂ) * w
  have hRpos : 0 < R := by
    have hc : 0 ≤ ‖c‖ := norm_nonneg c
    linarith
  have hRnonneg : 0 ≤ R := le_of_lt hRpos
  have hRne : ((R : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hRpos)
  have hnormR : ‖((R : ℝ) : ℂ)‖ = R := by
    simpa [abs_of_nonneg hRnonneg] using (Complex.norm_real R)
  have hcont : Continuous f := continuous_const.mul continuous_id
  have hconn_img : IsConnected (f '' E) :=
    isConnected_exterior.image f hcont.continuousOn
  have himage : f '' E = {z : ℂ | ‖z‖ > R} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      have hmul : R < R * ‖w‖ := by
        have h1 : R * 1 < R * ‖w‖ := mul_lt_mul_of_pos_left hw hRpos
        simpa using h1
      calc
        ‖((R : ℝ) : ℂ) * w‖ = ‖((R : ℝ) : ℂ)‖ * ‖w‖ := norm_mul _ _
        _ = R * ‖w‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hRnonneg]
        _ > R := hmul
    · intro z hz
      refine ⟨z / ((R : ℝ) : ℂ), ?_, ?_⟩
      · have hdiv : 1 < ‖z‖ / R := by
          exact (one_lt_div hRpos).2 (by simpa using hz)
        calc
          1 < ‖z‖ / R := hdiv
          _ = ‖z‖ / ‖R‖ := by rw [Real.norm_of_nonneg hRnonneg]
          _ = ‖z / ((R : ℝ) : ℂ)‖ := by
                simpa [Complex.norm_real] using (norm_div z (((R : ℝ) : ℂ))).symm
      · change (((R : ℝ) : ℂ) * (z / ((R : ℝ) : ℂ)) = z)
        field_simp [hRne]
  have hpre_img : IsPreconnected (f '' E) := hconn_img.isPreconnected
  simpa [f, E, R] using (himage ▸ hpre_img)

/-- Quotient analytic+real-scale payload forces quotient constancy on
outside-open (open mapping + one-dimensional image obstruction). -/
lemma outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticRealScalePayload
    (c : ℂ)
    (h_payload : OutsideOpenQuotientAnalyticRealScalePayload c) :
    OutsideOpenQuotientConstHypothesis c := by
  rcases h_payload with ⟨h_analytic, h_real⟩
  let U : Set ℂ := {z : ℂ | ‖z‖ > ‖c‖ + 2}
  let g : ℂ → ℂ := fun z => Quadratic.bottcher_map c z / z
  have hUpre : IsPreconnected U := by
    simpa [U] using isPreconnected_outside_open c
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    exact h_analytic z (by simpa [U] using hz)
  rcases (AnalyticOnNhd.is_constant_or_isOpen (g := g) hg hUpre) with ⟨q, hq⟩ | hopen
  · refine ⟨q, ?_⟩
    intro z hz
    exact hq z (by simpa [U] using hz)
  · have hUopen : IsOpen U := by
      simpa [U] using (isOpen_lt continuous_const continuous_norm)
    have hImgOpen : IsOpen (g '' U) := hopen U (by intro z hz; exact hz) hUopen
    let z0 : ℂ := ((‖c‖ + 3 : ℝ) : ℂ)
    have hz0 : ‖z0‖ > ‖c‖ + 2 := by
      have hnonneg : 0 ≤ ‖c‖ + 3 := by
        linarith [norm_nonneg c]
      have hnorm : ‖((‖c‖ + 3 : ℝ) : ℂ)‖ = ‖c‖ + 3 := by
        simpa [abs_of_nonneg hnonneg] using (Complex.norm_real (‖c‖ + 3))
      have hgt : ‖((‖c‖ + 3 : ℝ) : ℂ)‖ > ‖c‖ + 2 := by
        linarith
      simpa [z0] using hgt
    have hImgNonempty : (g '' U).Nonempty := by
      refine ⟨g z0, ?_⟩
      exact ⟨z0, by simpa [U] using hz0, rfl⟩
    rcases hImgNonempty with ⟨y, hyImg⟩
    have hyN : g '' U ∈ 𝓝 y := hImgOpen.mem_nhds hyImg
    rcases Metric.mem_nhds_iff.mp hyN with ⟨ε, hεpos, hεsub⟩
    let yI : ℂ := y + (((ε / 2 : ℝ) : ℂ) * Complex.I)
    have hyIball : yI ∈ Metric.ball y ε := by
      have hεhalf : ε / 2 < ε := by linarith
      have hdist : dist yI y = ε / 2 := by
        have hεhalf_nonneg : 0 ≤ ε / 2 := by linarith [hεpos]
        have hnormI : ‖(((ε / 2 : ℝ) : ℂ) * Complex.I)‖ = ε / 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hεhalf_nonneg, Complex.norm_I, mul_one]
        have hsub : yI - y = (((ε / 2 : ℝ) : ℂ) * Complex.I) := by
          simp [yI]
        calc
          dist yI y = ‖yI - y‖ := by simp [dist_eq_norm]
          _ = ‖(((ε / 2 : ℝ) : ℂ) * Complex.I)‖ := by rw [hsub]
          _ = ε / 2 := hnormI
      have : dist yI y < ε := by simpa [hdist] using hεhalf
      exact this
    have hyIimg : yI ∈ g '' U := hεsub hyIball
    rcases hyIimg with ⟨z, hzU, hzEq⟩
    rcases h_real z (by simpa [U] using hzU) with ⟨r, _hrpos, hrEq⟩
    have himz : Complex.im (g z) = 0 := by
      simpa [g, hrEq]
    have himyI_zero : Complex.im yI = 0 := by
      simpa [hzEq] using himz
    have himy_zero : Complex.im y = 0 := by
      rcases hyImg with ⟨zy, hzyU, hzyEq⟩
      rcases h_real zy (by simpa [U] using hzyU) with ⟨ry, _hrypos, hryEq⟩
      have himzy : Complex.im (g zy) = 0 := by
        simpa [g, hryEq]
      simpa [hzyEq] using himzy
    have himyI_half : Complex.im yI = ε / 2 := by
      simp [yI, himy_zero]
    exfalso
    linarith [himyI_zero, himyI_half, hεpos]

/-- Quotient analyticity on outside-open already implies quotient constancy,
since the real-scale quotient payload is unconditional. -/
lemma outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticityHypothesis
    (c : ℂ)
    (h_analytic : OutsideOpenQuotientAnalyticityHypothesis c) :
    OutsideOpenQuotientConstHypothesis c :=
  outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticRealScalePayload c
    ⟨h_analytic, outsideOpenQuotientRealScaleHypothesis_of_bottcher_map_div c⟩

/-- `c = 2` specialization: outside-open quotient analyticity implies quotient
constancy. -/
lemma outsideOpenQuotientConstHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo
    (h_analytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    OutsideOpenQuotientConstHypothesisTwo :=
  outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticityHypothesis (2 : ℂ)
    h_analytic

/-- Outside-open analyticity of `bottcher_map` implies quotient constancy. -/
lemma outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    OutsideOpenQuotientConstHypothesis c :=
  outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticityHypothesis c
    (outsideOpenQuotientAnalyticityHypothesis_of_outsideOpenAnalyticityHypothesis c h_analytic)

/-- `c = 2` specialization: outside-open analyticity implies quotient analyticity. -/
lemma outsideOpenQuotientAnalyticityHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    OutsideOpenQuotientAnalyticityHypothesisTwo :=
  outsideOpenQuotientAnalyticityHypothesis_of_outsideOpenAnalyticityHypothesis (2 : ℂ)
    h_analytic

/-- `c = 2` specialization: outside-open quotient analyticity implies
outside-open analyticity. -/
lemma outsideOpenAnalyticityHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    OutsideOpenAnalyticityHypothesis (2 : ℂ) :=
  outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientAnalyticityHypothesis (2 : ℂ)
    h_qanalytic

/-- `c = 2` specialization: outside-open analyticity implies quotient constancy. -/
lemma outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    OutsideOpenQuotientConstHypothesisTwo :=
  outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticityHypothesis (2 : ℂ)
    h_analytic

/-- There exists an outside-open point (explicit witness `‖c‖ + 3`). -/
lemma exists_outside_open_point (c : ℂ) :
    ∃ z : ℂ, ‖z‖ > ‖c‖ + 2 := by
  refine ⟨((‖c‖ + 3 : ℝ) : ℂ), ?_⟩
  have hnonneg : 0 ≤ ‖c‖ + 3 := by
    linarith [norm_nonneg c]
  have hnorm : ‖((‖c‖ + 3 : ℝ) : ℂ)‖ = ‖c‖ + 3 := by
    simpa [abs_of_nonneg hnonneg] using (Complex.norm_real (‖c‖ + 3))
  linarith

/-- There exists an outside-open point with positive real quotient value. -/
lemma exists_outside_open_point_with_real_scale_quotient (c : ℂ) :
    ∃ z : ℂ, ‖z‖ > ‖c‖ + 2 ∧
      ∃ r : ℝ, 0 < r ∧ Quadratic.bottcher_map c z / z = (r : ℂ) := by
  rcases exists_outside_open_point c with ⟨z, hz⟩
  rcases outsideOpenQuotientRealScaleHypothesis_of_bottcher_map_div c z hz with
    ⟨r, hrpos, hr⟩
  exact ⟨z, hz, r, hrpos, hr⟩

/-- Quotient constancy plus one positive-real outside-open quotient value yields
the strong quotient-rigidity witness. -/
lemma outsideOpenQuotientConstRealWitness_of_outsideOpenQuotientConstHypothesis
    (c : ℂ)
    (h_const : OutsideOpenQuotientConstHypothesis c) :
    OutsideOpenQuotientConstRealWitness c := by
  rcases h_const with ⟨q, hq⟩
  rcases exists_outside_open_point_with_real_scale_quotient c with
    ⟨z0, hz0, r, hrpos, hr0⟩
  have hq0 : Quadratic.bottcher_map c z0 / z0 = q := hq z0 hz0
  have hqeq : q = (r : ℂ) := by simpa [hq0] using hr0
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have hz_norm_pos : 0 < ‖z‖ := by
    linarith [hz, norm_nonneg c]
  have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz_norm_pos)
  have hqz : Quadratic.bottcher_map c z / z = q := hq z hz
  calc
    Quadratic.bottcher_map c z = (Quadratic.bottcher_map c z / z) * z := by
      field_simp [hz_ne]
    _ = q * z := by simp [hqz]
    _ = (r : ℂ) * z := by simpa [hqeq]

/-- `c = 2` specialization: quotient constancy implies the strong
quotient-rigidity witness. -/
lemma outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenQuotientConstHypothesisTwo
    (h_const : OutsideOpenQuotientConstHypothesisTwo) :
    OutsideOpenQuotientConstRealWitnessTwo :=
  outsideOpenQuotientConstRealWitness_of_outsideOpenQuotientConstHypothesis
    (2 : ℂ) h_const

/-- Outside-open analyticity already yields the strong quotient-rigidity
witness through quotient constancy. -/
lemma outsideOpenQuotientConstRealWitness_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    OutsideOpenQuotientConstRealWitness c :=
  outsideOpenQuotientConstRealWitness_of_outsideOpenQuotientConstHypothesis c
    (outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticityHypothesis c h_analytic)

/-- `c = 2` specialization: outside-open analyticity implies the strong
quotient-rigidity witness. -/
lemma outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenAnalyticityHypothesisTwo
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    OutsideOpenQuotientConstRealWitnessTwo :=
  outsideOpenQuotientConstRealWitness_of_outsideOpenAnalyticityHypothesis (2 : ℂ)
    h_analytic

/-- A strong quotient-rigidity witness implies outside-open analyticity. -/
lemma outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientConstRealWitness
    (c : ℂ)
    (h_wit : OutsideOpenQuotientConstRealWitness c) :
    OutsideOpenAnalyticityHypothesis c := by
  rcases h_wit with ⟨r, hr_pos, h_lin⟩
  intro z hz
  have hUopen : IsOpen {w : ℂ | ‖w‖ > ‖c‖ + 2} := by
    simpa using (isOpen_lt continuous_const continuous_norm)
  have hzU : z ∈ {w : ℂ | ‖w‖ > ‖c‖ + 2} := by simpa using hz
  have hUnhds : ({w : ℂ | ‖w‖ > ‖c‖ + 2} : Set ℂ) ∈ 𝓝 z :=
    hUopen.mem_nhds hzU
  have hEq :
      (fun w : ℂ => Quadratic.bottcher_map c w) =ᶠ[𝓝 z]
        (fun w : ℂ => (r : ℂ) * w) := by
    exact Filter.mem_of_superset hUnhds (by
      intro w hw
      exact h_lin w (by simpa using hw))
  have hLinAnalytic : AnalyticAt ℂ (fun w : ℂ => (r : ℂ) * w) z := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (analyticAt_const.mul analyticAt_id : AnalyticAt ℂ (fun w : ℂ => (r : ℂ) * w) z)
  exact hLinAnalytic.congr hEq.symm

/-- `c = 2` specialization: a strong quotient-rigidity witness implies
outside-open analyticity. -/
lemma outsideOpenAnalyticityHypothesisTwo_of_outsideOpenQuotientConstRealWitnessTwo
    (h_wit : OutsideOpenQuotientConstRealWitnessTwo) :
    OutsideOpenAnalyticityHypothesis (2 : ℂ) :=
  outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientConstRealWitness (2 : ℂ) h_wit

/-- A strong quotient-rigidity witness implies outside-open injectivity. -/
lemma injOn_outside_open_of_outsideOpenQuotientConstRealWitness
    (c : ℂ)
    (h_wit : OutsideOpenQuotientConstRealWitness c) :
    Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  rcases h_wit with ⟨r, hr_pos, h_lin⟩
  have hr_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hr_pos)
  intro z hz w hw hEq
  have hz_lin : Quadratic.bottcher_map c z = (r : ℂ) * z := h_lin z hz
  have hw_lin : Quadratic.bottcher_map c w = (r : ℂ) * w := h_lin w hw
  have hmul : (r : ℂ) * z = (r : ℂ) * w := by
    simpa [hz_lin, hw_lin] using hEq
  exact mul_left_cancel₀ hr_ne hmul

/-- A strong quotient-rigidity witness implies the combined non-slit
analytic/injective payload. -/
lemma outsideOpenAnalyticInjPayload_of_outsideOpenQuotientConstRealWitness
    (c : ℂ)
    (h_wit : OutsideOpenQuotientConstRealWitness c) :
    OutsideOpenAnalyticInjPayload c := by
  refine ⟨?_, ?_⟩
  · exact outsideOpenAnalyticityHypothesis_of_outsideOpenQuotientConstRealWitness c h_wit
  · exact injOn_outside_open_of_outsideOpenQuotientConstRealWitness c h_wit

/-- `c = 2` specialization: a strong quotient-rigidity witness implies the
combined non-slit analytic/injective payload. -/
lemma outsideOpenAnalyticInjNonSlitPayloadTwo_of_outsideOpenQuotientConstRealWitnessTwo
    (h_wit : OutsideOpenQuotientConstRealWitnessTwo) :
    OutsideOpenAnalyticInjNonSlitPayloadTwo :=
  outsideOpenAnalyticInjPayload_of_outsideOpenQuotientConstRealWitness (2 : ℂ) h_wit

/-- Outside-open analyticity alone yields the combined non-slit
analytic/injective payload via quotient constancy. -/
lemma outsideOpenAnalyticInjPayload_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    OutsideOpenAnalyticInjPayload c :=
  outsideOpenAnalyticInjPayload_of_outsideOpenQuotientConstRealWitness c
    (outsideOpenQuotientConstRealWitness_of_outsideOpenAnalyticityHypothesis c h_analytic)

/-- `c = 2` specialization: outside-open analyticity alone yields the combined
non-slit analytic/injective payload. -/
lemma outsideOpenAnalyticInjNonSlitPayloadTwo_of_outsideOpenAnalyticityHypothesisTwo
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    OutsideOpenAnalyticInjNonSlitPayloadTwo :=
  outsideOpenAnalyticInjPayload_of_outsideOpenAnalyticityHypothesis (2 : ℂ) h_analytic

/-- Combined outside-open analytic/injective payload implies quotient constancy. -/
lemma outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticInjPayload
    (c : ℂ)
    (h_payload : OutsideOpenAnalyticInjPayload c) :
    OutsideOpenQuotientConstHypothesis c :=
  outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticityHypothesis c
    (outsideOpenAnalyticityHypothesis_of_outsideOpenAnalyticInjPayload c h_payload)

/-- `c = 2` specialization: combined outside-open analytic/injective payload
implies quotient constancy. -/
lemma outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    OutsideOpenQuotientConstHypothesisTwo :=
  outsideOpenQuotientConstHypothesis_of_outsideOpenAnalyticInjPayload (2 : ℂ) h_payload

/-- `c = 2` specialization: combined outside-open analytic/injective payload
implies the strong quotient-rigidity witness. -/
lemma outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    OutsideOpenQuotientConstRealWitnessTwo :=
  outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenQuotientConstHypothesisTwo
    (outsideOpenQuotientConstHypothesisTwo_of_outsideOpenAnalyticInjNonSlitPayloadTwo h_payload)

/-- Outside-open exterior surjectivity from closed range plus the combined
outside-open analytic/injective seam payload. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_payload : OutsideOpenAnalyticInjPayload c) :
    BottcherSurjOnExteriorFromOutsideOpen c := by
  have hanalytic : OutsideOpenAnalyticityHypothesis c :=
    outsideOpenAnalyticityHypothesis_of_outsideOpenAnalyticInjPayload c h_payload
  have h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
    injOn_outside_open_of_outsideOpenAnalyticInjPayload c h_payload
  exact bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_analyticAt_of_deriv_ne_zero
    c hclosed hanalytic
    (bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn c hanalytic h_inj)

/-- `c = 2` specialization: outside-open exterior surjectivity from closed
range plus the combined non-slit outside-open analytic/injective payload. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (2 : ℂ) hclosed h_payload

/-- Outside-open exterior surjectivity from closed range plus the strong
quotient-rigidity witness. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_wit : OutsideOpenQuotientConstRealWitness c) :
    BottcherSurjOnExteriorFromOutsideOpen c :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    c hclosed (outsideOpenAnalyticInjPayload_of_outsideOpenQuotientConstRealWitness c h_wit)

/-- `c = 2` specialization: outside-open exterior surjectivity from closed range
plus the strong quotient-rigidity witness. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_wit : OutsideOpenQuotientConstRealWitnessTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness
    (2 : ℂ) hclosed h_wit

/-- `c = 2` specialization: outside-open exterior surjectivity from closed range
plus outside-open quotient constancy. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qconst : OutsideOpenQuotientConstHypothesisTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo
    hclosed (outsideOpenQuotientConstRealWitnessTwo_of_outsideOpenQuotientConstHypothesisTwo h_qconst)

/-- `c = 2` specialization: outside-open exterior surjectivity from closed range
plus outside-open quotient analyticity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
    hclosed (outsideOpenQuotientConstHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo h_qanalytic)

/-- Outside-open exterior surjectivity from closed range plus outside-open
analyticity, routed through the quotient-rigidity witness bridge. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    BottcherSurjOnExteriorFromOutsideOpen c :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness
    c hclosed
    (outsideOpenQuotientConstRealWitness_of_outsideOpenAnalyticityHypothesis c h_analytic)

/-- `c = 2` specialization: outside-open exterior surjectivity from closed range
plus outside-open analyticity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    (2 : ℂ) hclosed h_analytic

/-- Outside-open exterior surjectivity from restricted-map properness plus
outside-open analyticity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior c))
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    BottcherSurjOnExteriorFromOutsideOpen c :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    c (isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap c hproper) h_analytic

/-- `c = 2` specialization: outside-open exterior surjectivity from
restricted-map properness plus outside-open analyticity. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesisTwo
    (hproper : IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) :=
  bottcherSurjOnExteriorFromOutsideOpen_of_isProperMap_restrict_of_outsideOpenAnalyticityHypothesis
    (2 : ℂ) hproper h_analytic

/-- Outside-open `AnalyticAt` payload induces local charts inside outside-open
by taking the ambient outside-open set itself as the chart. -/
lemma outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis c := by
  intro z hz
  refine ⟨{w : ℂ | ‖w‖ > ‖c‖ + 2}, ?_, ?_, ?_, ?_⟩
  · simpa using (isOpen_lt continuous_const continuous_norm)
  · simpa using hz
  · intro w hw
    simpa using hw
  · intro w hw
    exact h_analytic w hw

/-- Build local analytic chart payload from neighborhood-level slit data. -/
lemma outsideOpenLocalAnalyticChartHypothesis_of_mem_nhds_slit
    (c : ℂ)
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z) :
    OutsideOpenLocalAnalyticChartHypothesis c := by
  intro z hz
  have hz_out : z ∈ {w : ℂ | ‖w‖ > ‖c‖ + 2} := by simpa using hz
  have hz_disk : z ∈ outside_disk c := outside_open_subset_outside_disk c hz_out
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c hz_disk
  rcases exists_open_subset_slit_orbit_basin_of_mem_nhds c z
      (hslit_nhds z hz) ((basin_of_infinity_isOpen c).mem_nhds hz_basin) with
    ⟨U, hUopen, hzU, hUsub⟩
  have hUslit : U ⊆ slit_orbit c := fun w hw => (hUsub hw).1
  have hUbasin : U ⊆ Quadratic.basin_of_infinity c := fun w hw => (hUsub hw).2
  exact ⟨U, hUopen, hzU, bottcher_map_analyticOnNhd_open c U hUopen hUslit hUbasin⟩

/-- Build outside-open analyticity payload from neighborhood-level slit data. -/
lemma outsideOpenAnalyticityHypothesis_of_mem_nhds_slit
    (c : ℂ)
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z) :
    OutsideOpenAnalyticityHypothesis c :=
  outsideOpenAnalyticityHypothesis_of_outsideOpenLocalAnalyticChartHypothesis c
    (outsideOpenLocalAnalyticChartHypothesis_of_mem_nhds_slit c hslit_nhds)

/-- `c = 2` specialization: local analytic-chart payload implies outside-open
analyticity payload. -/
lemma outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartHypothesis_two
    (h_chart : OutsideOpenLocalAnalyticChartHypothesis (2 : ℂ)) :
    OutsideOpenAnalyticityHypothesis (2 : ℂ) :=
  outsideOpenAnalyticityHypothesis_of_outsideOpenLocalAnalyticChartHypothesis (2 : ℂ) h_chart

/-- `c = 2` specialization: local analytic charts inside outside-open imply
outside-open local analytic charts. -/
lemma outsideOpenLocalAnalyticChartHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    OutsideOpenLocalAnalyticChartHypothesis (2 : ℂ) :=
  outsideOpenLocalAnalyticChartHypothesis_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    (2 : ℂ) h_chart

/-- `c = 2` specialization: local analytic charts inside outside-open imply the
outside-open analyticity payload. -/
lemma outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    OutsideOpenAnalyticityHypothesis (2 : ℂ) :=
  outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartHypothesis_two
    (outsideOpenLocalAnalyticChartHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two
      h_chart)

/-- CP2 constructive seam at `c = 2`: local charts inside outside-open yield
outside-open analyticity. -/
theorem outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    OutsideOpenAnalyticityHypothesis (2 : ℂ) :=
  outsideOpenAnalyticityHypothesis_two_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two
    h_chart

/-- CP2 constructive seam at `c = 2`: local charts inside outside-open yield
outside-open quotient analyticity. -/
theorem outsideOpenQuotientAnalyticityHypothesisTwo_constructive_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    OutsideOpenQuotientAnalyticityHypothesisTwo :=
  outsideOpenQuotientAnalyticityHypothesisTwo_of_outsideOpenAnalyticityHypothesisTwo
    (outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
      h_chart)

/-- CP2 constructive seam at `c = 2`: outside-open analyticity yields
outside-open quotient analyticity by division against `id` on outside-open. -/
theorem outsideOpenQuotientAnalyticityHypothesisTwo_constructive_of_outsideOpenAnalyticityHypothesis
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    OutsideOpenQuotientAnalyticityHypothesisTwo := by
  intro z hz
  have hz_norm_pos : 0 < ‖z‖ := by
    linarith [hz, norm_nonneg (2 : ℂ)]
  have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz_norm_pos)
  exact (h_analytic z hz).div analyticAt_id hz_ne

/-- CP2 constructive seam at `c = 2`: packaged quotient analyticity target from
the chart-within constructive input. -/
theorem outsideOpenQuotientAnalyticityHypothesisTwo_constructive
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ)) :
    OutsideOpenQuotientAnalyticityHypothesisTwo :=
  outsideOpenQuotientAnalyticityHypothesisTwo_constructive_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    h_chart

/-- CP2 constructive seam at `c = 2`: outside-open quotient analyticity yields
local analytic charts inside outside-open. -/
theorem outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_constructive_of_outsideOpenQuotientAnalyticityHypothesis
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ) :=
  outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_outsideOpenAnalyticityHypothesis
    (2 : ℂ)
    (outsideOpenAnalyticityHypothesisTwo_of_outsideOpenQuotientAnalyticityHypothesisTwo h_qanalytic)

/-- CP2 constructive seam at `c = 2`: outside-open quotient analyticity yields
outside-open analyticity through the chart-within bridge. -/
theorem outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenQuotientAnalyticityHypothesis
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    OutsideOpenAnalyticityHypothesis (2 : ℂ) :=
  outsideOpenAnalyticityHypothesisTwo_constructive_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
    (outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_constructive_of_outsideOpenQuotientAnalyticityHypothesis
      h_qanalytic)

/-- `c = 2` specialization: outside-open analyticity payload induces local
analytic charts inside outside-open. -/
lemma outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_two_of_outsideOpenAnalyticityHypothesis_two
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ) :=
  outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_outsideOpenAnalyticityHypothesis
    (2 : ℂ) h_analytic

/-- Construct external-ray data from closed range plus the stronger
outside-open local analytic-chart-within payload and outside-open injectivity. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis c)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open
    c hclosed
    (outsideOpenLocalAnalyticChartHypothesis_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis
      c h_chart)
    h_inj

/-- Construct external-ray data from closed range plus outside-open analyticity
by routing through the local-chart-within seam. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_via_localChartWithin_of_injOn_outside_open
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_analytic : OutsideOpenAnalyticityHypothesis c)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open
    c hclosed
    (outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_outsideOpenAnalyticityHypothesis
      c h_analytic)
    h_inj

/-- Construct external-ray data from closed range plus the combined outside-open
analytic/injective seam payload. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_payload : OutsideOpenAnalyticInjPayload c) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_via_localChartWithin_of_injOn_outside_open
    c hclosed
    (outsideOpenAnalyticityHypothesis_of_outsideOpenAnalyticInjPayload c h_payload)
    (injOn_outside_open_of_outsideOpenAnalyticInjPayload c h_payload)

/-- Construct external-ray data from closed range plus the strong
quotient-rigidity witness. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_wit : OutsideOpenQuotientConstRealWitness c) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    c hclosed
    (outsideOpenAnalyticInjPayload_of_outsideOpenQuotientConstRealWitness c h_wit)

/-- Construct external-ray data from closed range plus outside-open quotient
constancy. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_const : OutsideOpenQuotientConstHypothesis c) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness
    c hclosed
    (outsideOpenQuotientConstRealWitness_of_outsideOpenQuotientConstHypothesis c h_const)

/-- Construct external-ray data from closed range plus outside-open quotient
analyticity. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesis c) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis
    c hclosed
    (outsideOpenQuotientConstHypothesis_of_outsideOpenQuotientAnalyticityHypothesis
      c h_qanalytic)

/-- Construct external-ray data from closed range plus outside-open analyticity.
Injectivity is derived through the quotient-rigidity bridge. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (h_analytic : OutsideOpenAnalyticityHypothesis c) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    c hclosed
    (outsideOpenAnalyticInjPayload_of_outsideOpenAnalyticityHypothesis c h_analytic)

/-- `c = 2` specialization: construct external-ray data from closed range plus
outside-open `AnalyticAt` payload and outside-open injectivity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic :
      ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → AnalyticAt ℂ (Quadratic.bottcher_map (2 : ℂ)) z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open
    (2 : ℂ) hclosed h_analytic h_inj

/-- `c = 2` specialization: construct external-ray data from closed range plus
the strong quotient-rigidity witness. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitnessTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_wit : OutsideOpenQuotientConstRealWitnessTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientConstRealWitness
    (2 : ℂ) hclosed h_wit

/-- `c = 2` specialization: construct external-ray data from closed range plus
outside-open quotient constancy. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_const : OutsideOpenQuotientConstHypothesisTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientConstHypothesis
    (2 : ℂ) hclosed h_const

/-- `c = 2` specialization: construct external-ray data from closed range plus
outside-open quotient analyticity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_qanalytic : OutsideOpenQuotientAnalyticityHypothesisTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenQuotientAnalyticityHypothesis
    (2 : ℂ) hclosed h_qanalytic

/-- `c = 2` specialization: construct external-ray data from closed range plus
outside-open analyticity and outside-open injectivity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis
    (2 : ℂ) hclosed h_analytic

/-- Compatibility wrapper retaining the older signature that included an explicit
outside-open injectivity assumption. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesis_of_injOn_outside_open
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_analytic : OutsideOpenAnalyticityHypothesis (2 : ℂ))
    (_h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticityHypothesisTwo
    hclosed h_analytic

/-- `c = 2` specialization from the combined non-slit outside-open
analytic/injective seam payload. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenAnalyticInjNonSlitPayloadTwo
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_payload : OutsideOpenAnalyticInjNonSlitPayloadTwo) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenAnalyticInjPayload
    (2 : ℂ) hclosed h_payload

/-- `c = 2` specialization: construct external-ray data from closed range plus
outside-open local analytic charts and outside-open injectivity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_chart : OutsideOpenLocalAnalyticChartHypothesis (2 : ℂ))
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartHypothesis_of_injOn_outside_open
    (2 : ℂ) hclosed h_chart h_inj

/-- `c = 2` specialization: construct external-ray data from closed range plus
outside-open local analytic charts inside outside-open and outside-open injectivity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (h_chart : OutsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis (2 : ℂ))
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_outsideOpenLocalAnalyticChartWithinOutsideOpenHypothesis_of_injOn_outside_open
    (2 : ℂ) hclosed h_chart h_inj

/-- Local-slit wrapper for outside-open derivative nonvanishing from injectivity. -/
lemma bottcher_map_deriv_ne_zero_on_outside_open_of_mem_nhds_slit_of_injOn
    (c : ℂ)
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    ∀ z, ‖z‖ > ‖c‖ + 2 → deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  exact bottcher_map_deriv_ne_zero_on_outside_open_of_analyticAt_of_injOn c
    (bottcher_map_analyticAt_on_outside_open_of_mem_nhds_slit c hslit_nhds) h_inj

/-- Local-slit wrapper for external-ray data construction from restricted-map
closed-range and outside-open injectivity. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2}) :
    Quadratic.ExternalRayMapData c := by
  exact external_ray_map_data_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open c
    hclosed
    (bottcher_map_analyticAt_on_outside_open_of_mem_nhds_slit c hslit_nhds)
    h_inj

/-- `c = 2` specialization: external-ray data from closed range, local-slit
neighborhood payload, and outside-open injectivity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hslit_nhds : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z)
    (h_inj : Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open
    (2 : ℂ) hclosed hslit_nhds h_inj

/-- External-ray data from closed range, local-slit neighborhoods, and the
iterate-left-inverse injectivity route. -/
theorem external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse
    (c : ℂ)
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior c)))
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin c) :
    Quadratic.ExternalRayMapData c :=
  external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_injOn_outside_open
    c hclosed hslit_nhds
    (bottcher_map_inj_on_outside_open_of_iter_left_inverse c h_left_iter)

/-- `c = 2` specialization: external-ray data from closed range, local-slit
neighborhoods, and iterate-left-inverse injectivity. -/
theorem external_ray_map_data_two_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse
    (hclosed : IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ))))
    (hslit_nhds : ∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_data_of_isClosedRange_restrict_of_mem_nhds_slit_of_iter_left_inverse
    (2 : ℂ) hclosed hslit_nhds h_left_iter

lemma bottcher_map_local_inj_of_deriv_ne_zero_of_mem_nhds_slit_basin
    (c z₀ : ℂ)
    (hslit : slit_orbit c ∈ 𝓝 z₀)
    (hbasin : Quadratic.basin_of_infinity c ∈ 𝓝 z₀)
    (hderiv : deriv (Quadratic.bottcher_map c) z₀ ≠ 0) :
    ∃ s ∈ 𝓝 z₀, Set.InjOn (Quadratic.bottcher_map c) s := by
  exact injOn_nhds_of_analyticAt
    (bottcher_map_analyticAt_of_mem_nhds_slit_basin c z₀ hslit hbasin) hderiv

lemma bottcher_map_isLocalHomeomorphOn_basin_of_deriv_ne_zero_of_mem_nhds_slit
    (c : ℂ)
    (hslit : ∀ z, z ∈ Quadratic.basin_of_infinity c → slit_orbit c ∈ 𝓝 z)
    (hderiv : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      deriv (Quadratic.bottcher_map c) z ≠ 0) :
    IsLocalHomeomorphOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  refine isLocalHomeomorphOn_of_analytic_deriv_ne_zero ?_ hderiv
  intro z hz
  exact bottcher_map_analyticAt_of_mem_nhds_slit_basin c z
    (hslit z hz) ((basin_of_infinity_isOpen c).mem_nhds hz)

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

/-- Neighborhood-level slit-orbit payload implies global outside-open slit
inclusion. -/
lemma outside_open_subset_slit_orbit_of_mem_nhds_slit
    (c : ℂ)
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit c ∈ 𝓝 z) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c := by
  intro z hz
  exact mem_of_mem_nhds (hslit_nhds z hz)

/-- Rotated neighborhood-level slit-orbit payload implies global outside-open
inclusion in the corresponding rotated slit orbit. -/
lemma outside_open_subset_slit_orbit_rot_of_mem_nhds_slit
    (c : ℂ) (θ : ℝ)
    (hslit_nhds : ∀ z, ‖z‖ > ‖c‖ + 2 → slit_orbit_rot c θ ∈ 𝓝 z) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit_rot c θ := by
  intro z hz
  exact mem_of_mem_nhds (hslit_nhds z hz)

/-- No-go checkpoint (rotated variant): global outside-open inclusion in any
rotated slit orbit is impossible in the current model. -/
lemma not_outside_open_subset_slit_orbit_rot (c : ℂ) (θ : ℝ) :
    ¬ ({z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit_rot c θ) := by
  intro hslit
  let a : ℝ := ‖c‖ + 3
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith [norm_nonneg c]
  let z0 : ℂ := ((-a : ℝ) : ℂ) * Complex.exp (Complex.I * θ)
  have hz0_out : ‖z0‖ > ‖c‖ + 2 := by
    have hnorm : ‖z0‖ = a := by
      calc
        ‖z0‖ = ‖((-a : ℝ) : ℂ)‖ * ‖Complex.exp (Complex.I * θ)‖ := by
          simpa [z0] using (norm_mul (((-a : ℝ) : ℂ)) (Complex.exp (Complex.I * θ)))
        _ = |(-a : ℝ)| * 1 := by simp
        _ = a := by
          rw [abs_of_nonpos]
          · ring
          · linarith
    have hnorm' : ‖z0‖ = ‖c‖ + 3 := by simpa [a] using hnorm
    linarith
  have hz0_slit_orbit : z0 ∈ slit_orbit_rot c θ := hslit hz0_out
  have hz0_slit : z0 * Complex.exp (-Complex.I * θ) ∈ Complex.slitPlane := by
    simpa [slit_orbit_rot, slitPlaneRot] using hz0_slit_orbit 0
  have hz0_arg : Complex.arg (((-a : ℝ) : ℂ)) = Real.pi := by
    have hneg : (-a : ℝ) < 0 := by linarith
    simpa using (Complex.arg_ofReal_of_neg hneg)
  have hExpMul :
      Complex.exp (Complex.I * θ) * Complex.exp (-Complex.I * θ) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hz0_mul :
      z0 * Complex.exp (-Complex.I * θ) = (((-a : ℝ) : ℂ)) := by
    dsimp [z0]
    calc
      (((-a : ℝ) : ℂ) * Complex.exp (Complex.I * θ)) * Complex.exp (-Complex.I * θ)
          = (((-a : ℝ) : ℂ)) * (Complex.exp (Complex.I * θ) * Complex.exp (-Complex.I * θ)) := by
              ac_rfl
      _ = (((-a : ℝ) : ℂ)) * 1 := by rw [hExpMul]
      _ = (((-a : ℝ) : ℂ)) := by simp
  have hz0_slit' : (((-a : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    exact hz0_mul ▸ hz0_slit
  exact (Complex.mem_slitPlane_iff_arg.mp hz0_slit').1 hz0_arg

/-- No-go checkpoint: global slit inclusion on outside-open is impossible in
the current principal-slit model. -/
lemma not_outside_open_subset_slit_orbit (c : ℂ) :
    ¬ ({z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) := by
  intro hslit
  let z0 : ℂ := ((-(‖c‖ + 3 : ℝ)) : ℂ)
  have hz0_out : ‖z0‖ > ‖c‖ + 2 := by
    have hnorm : ‖z0‖ = ‖c‖ + 3 := by
      have hnorm_abs : ‖z0‖ = |-(‖c‖ + 3 : ℝ)| := by
        simpa [z0] using (Complex.norm_real (-(‖c‖ + 3 : ℝ)))
      rw [hnorm_abs]
      rw [abs_of_nonpos]
      · ring_nf
      · linarith [norm_nonneg c]
    linarith
  have hz0_slit_orbit : z0 ∈ slit_orbit c := hslit hz0_out
  have hz0_slit : z0 ∈ Complex.slitPlane := hz0_slit_orbit 0
  have hz0_arg : Complex.arg z0 = Real.pi := by
    have hneg : (-(‖c‖ + 3 : ℝ)) < 0 := by
      have hc : 0 ≤ ‖c‖ := norm_nonneg c
      linarith
    simpa [z0] using (Complex.arg_ofReal_of_neg hneg)
  exact (Complex.mem_slitPlane_iff_arg.mp hz0_slit).1 hz0_arg

/-- `c = 2` specialization of the no-go checkpoint for global outside-open slit
inclusion. -/
lemma not_outside_open_subset_slit_orbit_two :
    ¬ ({z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} ⊆ slit_orbit (2 : ℂ)) := by
  exact not_outside_open_subset_slit_orbit (2 : ℂ)

/-- Consequently, neighborhood-level slit payload on all outside-open points is
impossible at `c = 2`. -/
lemma not_mem_nhds_slit_on_outside_open_two :
    ¬ (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit (2 : ℂ) ∈ 𝓝 z) := by
  intro hslit_nhds
  exact not_outside_open_subset_slit_orbit_two
    (outside_open_subset_slit_orbit_of_mem_nhds_slit (2 : ℂ) hslit_nhds)

/-- Rotated variant at `c = 2`: neighborhood-level rotated slit payload on all
outside-open points is impossible. -/
lemma not_mem_nhds_slit_rot_on_outside_open_two (θ : ℝ) :
    ¬ (∀ z, ‖z‖ > ‖(2 : ℂ)‖ + 2 → slit_orbit_rot (2 : ℂ) θ ∈ 𝓝 z) := by
  intro hslit_nhds
  exact not_outside_open_subset_slit_orbit_rot (2 : ℂ) θ
    (outside_open_subset_slit_orbit_rot_of_mem_nhds_slit (2 : ℂ) θ hslit_nhds)
end MLC
