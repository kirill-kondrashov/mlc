import Mlc.Quadratic.Complex.Bottcher.BottcherOnMDefs
import Mlc.Quadratic.Complex.Bottcher.CpowSlit
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Normed.Group.Tannery

namespace MLC

open Quadratic Complex Topology Set Filter
open scoped BigOperators

def atInfinity : Filter ℂ :=
  Filter.comap (fun z : ℂ => ‖z‖) atTop

lemma continuous_quadratic_map (c : ℂ) : Continuous (quadratic_map c) := by
  have h_pow : Continuous (fun z : ℂ => z ^ 2) := continuous_id.pow 2
  have h_add : Continuous (fun z : ℂ => z ^ 2 + c) :=
    h_pow.add continuous_const
  simpa [quadratic_map] using h_add

lemma quadratic_map_differentiable (c : ℂ) :
    Differentiable ℂ (quadratic_map c) := by
  unfold quadratic_map
  exact (differentiable_id.pow 2).add_const c

lemma quadratic_map_norm_lower (c z : ℂ) :
    ‖quadratic_map c z‖ ≥ ‖z‖ ^ 2 - ‖c‖ := by
  have h :
      ‖z ^ 2‖ ≤ ‖quadratic_map c z‖ + ‖c‖ := by
    have h' := norm_add_le (quadratic_map c z) (-c)
    simpa [quadratic_map, add_comm, add_left_comm, add_assoc] using h'
  have h' : ‖z ^ 2‖ - ‖c‖ ≤ ‖quadratic_map c z‖ :=
    sub_le_iff_le_add.mpr h
  simpa [norm_pow] using h'

lemma quadratic_map_norm_ge_of_norm_ge
    (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 1) :
    ‖quadratic_map c z‖ ≥ ‖z‖ := by
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic_map c z‖ :=
    quadratic_map_norm_lower c z
  have h2 : ‖z‖ ≤ ‖z‖ ^ 2 - ‖c‖ := by
    calc
      ‖z‖ ≤ ‖z‖ ^ 2 - (‖z‖ - 1) := by
        have hsq : 0 ≤ (‖z‖ - 1) ^ 2 := by nlinarith
        nlinarith [hsq]
      _ ≤ ‖z‖ ^ 2 - ‖c‖ := by nlinarith
  exact le_trans h2 h1

lemma quadratic_map_norm_ge_add_one
    (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    ‖quadratic_map c z‖ ≥ ‖z‖ + 1 := by
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic_map c z‖ :=
    quadratic_map_norm_lower c z
  have hy : ‖c‖ ≤ ‖z‖ - 2 := by nlinarith
  have h2a : ‖z‖ ^ 2 - (‖z‖ - 2) ≤ ‖z‖ ^ 2 - ‖c‖ := by
    nlinarith [hy]
  have h2b : ‖z‖ + 1 ≤ ‖z‖ ^ 2 - (‖z‖ - 2) := by
    have hsq : 0 ≤ (‖z‖ - 1) ^ 2 := by nlinarith
    nlinarith [hsq]
  exact le_trans (le_trans h2b h2a) h1

lemma iterate_quadratic_map_norm_ge_add
    (c z : ℂ) :
    ∀ n, ‖z‖ ≥ ‖c‖ + 2 →
      ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := by
  intro n
  induction n with
  | zero =>
      intro hz
      simp
  | succ n ih =>
      intro hz
      have h0 : ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := ih hz
      have h_ge : ‖(quadratic_map c)^[n] z‖ ≥ ‖c‖ + 2 := by
        have h1 : ‖c‖ + 2 ≤ ‖z‖ := by nlinarith
        exact le_trans h1 (le_trans (by nlinarith) h0)
      have h1 : ‖quadratic_map c ((quadratic_map c)^[n] z)‖ ≥
          ‖(quadratic_map c)^[n] z‖ + 1 :=
        quadratic_map_norm_ge_add_one c _ h_ge
      have h2 : ‖(quadratic_map c)^[n] z‖ + 1 ≥ ‖z‖ + (n + 1) := by
        nlinarith
      rw [Function.iterate_succ_apply']
      simpa [Nat.cast_add, Nat.cast_one] using le_trans h2 h1

lemma iterate_quadratic_map_norm_ge
    (c z : ℂ) (n : ℕ) (hz : ‖z‖ ≥ ‖c‖ + 1) :
    ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih
        (quadratic_map_norm_ge_of_norm_ge c _ (le_trans hz ih))

lemma iterate_quadratic_map_tendsto_infty
    (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
  have hmono : ∀ n, ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := by
    intro n
    exact iterate_quadratic_map_norm_ge_add c z n hz
  have h1 : Tendsto (fun n : ℕ => ‖z‖ + n) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
      simpa using (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    apply tendsto_atTop_mono (fun n => ?_) hnat
    nlinarith [norm_nonneg z]
  exact tendsto_atTop_mono hmono h1

lemma eventually_atInfinity_norm_gt (R : ℝ) :
    ∀ᶠ z : ℂ in atInfinity, R < ‖z‖ := by
  dsimp [atInfinity]
  have hR : ∀ᶠ r in (atTop : Filter ℝ), R < r :=
    Filter.eventually_atTop.2 ⟨R + 1, by intro r hr; linarith⟩
  refine (Filter.eventually_comap).2 ?_
  refine hR.mono ?_
  intro r hr z hz
  simpa [hz] using hr

lemma tendsto_atInfinity_norm_pow_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => ‖z‖ ^ k) atInfinity atTop := by
  refine tendsto_atTop.2 ?_
  intro R
  by_cases hR : R ≤ 0
  · exact Filter.Eventually.of_forall
      (fun z => le_trans hR (pow_nonneg (norm_nonneg _) _))
  have hlarge : ∀ᶠ z in atInfinity, max 1 R < ‖z‖ :=
    eventually_atInfinity_norm_gt (max 1 R)
  refine hlarge.mono ?_
  intro z hz
  have hz1 : (1 : ℝ) ≤ ‖z‖ :=
    le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz)
  have hzR : R ≤ ‖z‖ :=
    le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨n, rfl⟩
  have hpow1 : (1 : ℝ) ≤ ‖z‖ ^ n := one_le_pow₀ hz1
  have hpow : ‖z‖ ≤ ‖z‖ ^ (n + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hpow1 (norm_nonneg z)
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact le_trans hzR hpow

lemma tendsto_atInfinity_inv_pow_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => (z ^ k)⁻¹) atInfinity (𝓝 (0 : ℂ)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have hpow : Tendsto (fun z : ℂ => ‖z ^ k‖) atInfinity atTop := by
    simpa [norm_pow] using tendsto_atInfinity_norm_pow_atTop k hk
  have hpow_inv : Tendsto (fun z : ℂ => (‖z ^ k‖)⁻¹) atInfinity (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow
  simpa [norm_inv] using hpow_inv

lemma tendsto_atInfinity_const_div_pow_zero (c : ℂ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ => c / z ^ k) atInfinity (𝓝 (0 : ℂ)) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_atInfinity_inv_pow_zero k hk))

lemma tendsto_quadratic_iter_div_pow_atInfinity (c : ℂ) :
    ∀ N, Tendsto (fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)) atInfinity
      (𝓝 (1 : ℂ))
  | 0 => by
      have hne : ∀ᶠ z in atInfinity, z ≠ 0 :=
        (eventually_atInfinity_norm_gt 0).mono
          (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
      refine (tendsto_congr' ?_).1 tendsto_const_nhds
      filter_upwards [hne] with z hz
      simp [hz]
  | N + 1 => by
      have hN : Tendsto
          (fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)) atInfinity
          (𝓝 (1 : ℂ)) :=
        tendsto_quadratic_iter_div_pow_atInfinity c N
      let g : ℂ → ℂ := fun z => (quadratic_map c)^[N] z / z ^ (2 ^ N)
      have hsq : Tendsto (fun z => (g z) ^ 2) atInfinity (𝓝 (1 : ℂ)) := by
        simpa using ((continuous_id.pow 2).tendsto (1 : ℂ)).comp hN
      have hsmall : Tendsto (fun z => c / z ^ (2 ^ (N + 1))) atInfinity
          (𝓝 (0 : ℂ)) := by
        exact tendsto_atInfinity_const_div_pow_zero c _ (pow_pos (by norm_num) _)
      have hsum :
          Tendsto (fun z => (g z) ^ 2 + c / z ^ (2 ^ (N + 1))) atInfinity
            (𝓝 (1 : ℂ)) := by
        simpa using hsq.add hsmall
      refine (tendsto_congr' ?_).1 hsum
      refine Filter.Eventually.of_forall ?_
      intro z
      have hpow : z ^ (2 ^ (N + 1)) = (z ^ (2 ^ N)) ^ 2 := by
        simp [pow_succ, pow_mul]
      have hdiv :
          ((quadratic_map c)^[N] z) ^ 2 / z ^ (2 ^ (N + 1)) =
            (g z) ^ 2 := by
        rw [hpow]
        simpa [g, pow_two] using
          (div_pow (a := (quadratic_map c)^[N] z)
            (b := z ^ (2 ^ N)) (n := 2)).symm
      simp [quadratic_map, Function.iterate_succ_apply', add_div, hdiv, g]

lemma eventually_atInfinity_iter_ne_zero (c : ℂ) (n : ℕ) :
    ∀ᶠ z in atInfinity, (quadratic_map c)^[n] z ≠ 0 := by
  filter_upwards [eventually_atInfinity_norm_gt (‖c‖ + 2)] with z hz
  apply (norm_ne_zero_iff).1
  have hiter := iterate_quadratic_map_norm_ge c z n (by linarith)
  exact ne_of_gt (lt_of_lt_of_le (by linarith [norm_nonneg c]) hiter)

lemma potential_seq_eq_log_norm_iterate
    (c z : ℂ) (n : ℕ)
    (h1 : 1 ≤ ‖(quadratic_map c)^[n] z‖) :
    Quadratic.potential_seq c z n =
      (1 / 2 ^ n) * Real.log ‖(quadratic_map c)^[n] z‖ := by
  dsimp [Quadratic.potential_seq]
  have hmax : max 1 ‖(quadratic_map c)^[n] z‖ =
      ‖(quadratic_map c)^[n] z‖ :=
    max_eq_right h1
  change
    (1 / 2 ^ n) * Real.log (max 1 ‖(quadratic_map c)^[n] z‖) =
      (1 / 2 ^ n) * Real.log ‖(quadratic_map c)^[n] z‖
  rw [hmax]

lemma tendsto_norm_quadratic_iter_div_pow_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto (fun z => ‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N))
      atInfinity (𝓝 (1 : ℝ)) := by
  have h := tendsto_quadratic_iter_div_pow_atInfinity c N
  have hnorm :
      Tendsto
        (fun z : ℂ => ‖(quadratic_map c)^[N] z / z ^ (2 ^ N)‖)
        atInfinity (𝓝 (‖(1 : ℂ)‖)) :=
    (continuous_norm.tendsto (1 : ℂ)).comp h
  simpa [norm_div, norm_pow] using hnorm

lemma tendsto_log_norm_quadratic_iter_div_pow_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto
      (fun z => Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)))
      atInfinity (𝓝 (0 : ℝ)) := by
  have h := tendsto_norm_quadratic_iter_div_pow_atInfinity c N
  simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h

lemma tendsto_potential_seq_minus_log_norm_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto
        (fun z =>
          (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ -
            Real.log ‖z‖)
        atInfinity (𝓝 (0 : ℝ)) := by
  have hlog := tendsto_log_norm_quadratic_iter_div_pow_atInfinity c N
  have hne : ∀ᶠ z in atInfinity, ‖z‖ ≠ 0 :=
    (eventually_atInfinity_norm_gt 0).mono (fun _ hz => ne_of_gt hz)
  have hne' : ∀ᶠ z in atInfinity, ‖(quadratic_map c)^[N] z‖ ≠ 0 :=
    (eventually_atInfinity_iter_ne_zero c N).mono
      (fun _ hz => by simpa using (norm_ne_zero_iff.mpr hz))
  have hsplit :
      ∀ᶠ z in atInfinity,
        (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ -
            Real.log ‖z‖ =
          (1 / (2 : ℝ) ^ N) *
            Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) := by
    refine (hne'.and hne).mono ?_
    intro z hz
    rcases hz with ⟨hne', hne⟩
    have hlogdiv :
        Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) =
          Real.log ‖(quadratic_map c)^[N] z‖ -
            (2 ^ N : ℝ) * Real.log ‖z‖ := by
      have hlogdiv' :
          Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) =
            Real.log ‖(quadratic_map c)^[N] z‖ -
              Real.log (‖z‖ ^ (2 ^ N)) :=
        Real.log_div hne' (pow_ne_zero (2 ^ N) hne)
      have hlogpow :
          Real.log (‖z‖ ^ (2 ^ N)) = (2 ^ N : ℕ) * Real.log ‖z‖ :=
        Real.log_pow ‖z‖ (2 ^ N)
      calc
        Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N))
            = Real.log ‖(quadratic_map c)^[N] z‖ -
                Real.log (‖z‖ ^ (2 ^ N)) := hlogdiv'
        _ = Real.log ‖(quadratic_map c)^[N] z‖ -
              (2 ^ N : ℝ) * Real.log ‖z‖ := by simp [hlogpow]
    calc
      (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ -
          Real.log ‖z‖ =
          (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ -
            (1 / (2 : ℝ) ^ N) * ((2 ^ N : ℝ) * Real.log ‖z‖) := by
            simp
      _ = (1 / (2 : ℝ) ^ N) *
            (Real.log ‖(quadratic_map c)^[N] z‖ -
              (2 ^ N : ℝ) * Real.log ‖z‖) := by ring
      _ = (1 / (2 : ℝ) ^ N) *
            Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)) := by
              rw [hlogdiv]
  have hmul :
      Tendsto
          (fun z =>
            (1 / (2 : ℝ) ^ N) *
              Real.log (‖(quadratic_map c)^[N] z‖ / ‖z‖ ^ (2 ^ N)))
          atInfinity (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hlog)
  exact (tendsto_congr' hsplit).2 hmul

lemma tendsto_green_function_minus_log_norm_atInfinity (c : ℂ) :
    Tendsto (fun z => green_function c z - Real.log ‖z‖)
      atInfinity (𝓝 (0 : ℝ)) := by
  refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
  have hgoal :
      Tendsto (fun z => |green_function c z - Real.log ‖z‖|)
        atInfinity (𝓝 (0 : ℝ)) := by
    refine (tendsto_order.2 ⟨?_, ?_⟩)
    · intro a ha
      exact Filter.Eventually.of_forall
        (fun z => lt_of_lt_of_le ha (abs_nonneg _))
    · intro a ha
      have ha' : 0 < a / 2 := by nlinarith
      let M : ℝ := 2 * ‖c‖ / (escape_bound c) ^ 2
      have hpow0 :
          Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hpow :
          Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * M) atTop (𝓝 (0 : ℝ)) :=
        by simpa using hpow0.mul tendsto_const_nhds
      have hball : Metric.ball (0 : ℝ) (a / 2) ∈ 𝓝 (0 : ℝ) :=
        Metric.ball_mem_nhds _ ha'
      rcases Filter.eventually_atTop.1 (tendsto_def.1 hpow _ hball) with
        ⟨N, hN⟩
      have hNbound : (2 ^ N : ℝ)⁻¹ * M < a / 2 := by
        have h := hN N le_rfl
        have hM : 0 ≤ M := by
          exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg c))
            (sq_nonneg _)
        have h' : |(1 / 2 : ℝ) ^ N| * |M| < a / 2 := by
          simpa [Metric.ball, Real.dist_eq, abs_mul] using h
        have h'' : |(1 / 2 : ℝ) ^ N| * M < a / 2 := by
          simpa [abs_of_nonneg hM] using h'
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
        have h''' : (1 / 2 : ℝ) ^ N * M < a / 2 := by
          simpa [abs_of_nonneg hpow_nonneg] using h''
        simpa [one_div, inv_pow] using h'''
      have hpot : ∀ᶠ z in atInfinity,
          |(1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ -
            Real.log ‖z‖| < a / 2 := by
        have hpot' := tendsto_potential_seq_minus_log_norm_atInfinity c N
        simpa [Metric.ball, Real.dist_eq] using
          (tendsto_def.1 hpot' _ (Metric.ball_mem_nhds _ ha'))
      have hesc : ∀ᶠ z in atInfinity, ‖z‖ > escape_bound c :=
        eventually_atInfinity_norm_gt (escape_bound c)
      refine (hpot.and hesc).mono ?_
      intro z hz
      rcases hz with ⟨hpotz, hzesc⟩
      have hescN : ‖(quadratic_map c)^[N] z‖ > escape_bound c := by
        exact norm_orbit_gt_escape_bound_of_ge c z 0 N (Nat.zero_le _) (by
          simpa [Quadratic.orbit] using hzesc)
      have hdist :
          dist (Quadratic.potential_seq c z N) (Quadratic.green_function c z) ≤
            (2 ^ N : ℝ)⁻¹ * M := by
        simpa [M, one_div, inv_pow, Quadratic.orbit] using
          (dist_potential_seq_green_function_le_of_escaping c z N hescN)
      have h1 : 1 ≤ ‖(quadratic_map c)^[N] z‖ := by
        have htwo : (2 : ℝ) ≤ escape_bound c :=
          le_trans (R_ge_two c) (escape_bound_ge_R c)
        exact le_trans (by linarith) (le_of_lt hescN)
      have hpot_eq :
          Quadratic.potential_seq c z N =
            (1 / (2 : ℝ) ^ N) * Real.log ‖(quadratic_map c)^[N] z‖ :=
        potential_seq_eq_log_norm_iterate c z N h1
      have hpotz' :
          |Quadratic.potential_seq c z N - Real.log ‖z‖| < a / 2 := by
        simpa [hpot_eq] using hpotz
      have hdist' :
          |Quadratic.green_function c z - Quadratic.potential_seq c z N| ≤
            (2 ^ N : ℝ)⁻¹ * M := by
        simpa [Real.dist_eq, abs_sub_comm] using hdist
      have htri :
          |Quadratic.green_function c z - Real.log ‖z‖| ≤
            |Quadratic.green_function c z - Quadratic.potential_seq c z N| +
              |Quadratic.potential_seq c z N - Real.log ‖z‖| :=
        abs_sub_le _ _ _
      have hle :
          |Quadratic.green_function c z - Real.log ‖z‖| ≤
            (2 ^ N : ℝ)⁻¹ * M + a / 2 :=
        htri.trans (add_le_add hdist' (le_of_lt hpotz'))
      have hlt : (2 ^ N : ℝ)⁻¹ * M + a / 2 < a := by
        have h := add_lt_add_right hNbound (a / 2)
        nlinarith
      exact lt_of_le_of_lt hle hlt
  simpa [Real.norm_eq_abs] using hgoal

noncomputable def nearOneLogCorrection (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ((2 : ℂ) ^ (N + 1))⁻¹ *
    Complex.log
      ((1 : ℂ) +
        (c / z ^ (2 ^ (N + 1))) /
          ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)

lemma tendsto_nearOneLogCorrection_atInfinity (c : ℂ) (N : ℕ) :
    Tendsto (nearOneLogCorrection c N) atInfinity (𝓝 (0 : ℂ)) := by
  have hterm :
      Tendsto
        (fun z : ℂ => (c / z ^ (2 ^ (N + 1))) /
          ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
        atInfinity (𝓝 (0 : ℂ)) := by
    have hsmall :
        Tendsto (fun z : ℂ => c / z ^ (2 ^ (N + 1))) atInfinity (𝓝 (0 : ℂ)) :=
      tendsto_atInfinity_const_div_pow_zero c _ (pow_pos (by norm_num) _)
    have hratio :
        Tendsto (fun z : ℂ => (quadratic_map c)^[N] z / z ^ (2 ^ N))
          atInfinity (𝓝 (1 : ℂ)) :=
      tendsto_quadratic_iter_div_pow_atInfinity c N
    have hsq : Tendsto
        (fun z : ℂ => ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
        atInfinity (𝓝 (1 : ℂ)) := by
      simpa using ((continuous_id.pow 2).tendsto (1 : ℂ)).comp hratio
    have hinv : Tendsto
        (fun z : ℂ => (((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)⁻¹)
        atInfinity (𝓝 (1 : ℂ)) :=
      by
        have hcont :
            ContinuousAt (fun w : ℂ => (w ^ 2)⁻¹) (1 : ℂ) := by
          exact (ContinuousAt.inv₀ ((continuous_id.pow 2).continuousAt) (by norm_num))
        simpa [Function.comp_apply] using hcont.tendsto.comp hratio
    simpa [div_eq_mul_inv] using hsmall.mul hinv
  have hlog :
      Tendsto
        (fun z : ℂ => Complex.log
          ((1 : ℂ) +
            (c / z ^ (2 ^ (N + 1))) /
              ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
        atInfinity (𝓝 (0 : ℂ)) := by
    have harg :
        Tendsto
            (fun z : ℂ =>
              (1 : ℂ) +
                (c / z ^ (2 ^ (N + 1))) /
                  ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
            atInfinity (𝓝 (1 : ℂ)) := by
      have hconst : Tendsto (fun _ : ℂ => (1 : ℂ)) atInfinity (𝓝 (1 : ℂ)) :=
        tendsto_const_nhds
      simpa using hconst.add hterm
    simpa using tendsto_log_of_tendsto_slitPlane
      (f := fun z : ℂ =>
        (1 : ℂ) +
          (c / z ^ (2 ^ (N + 1))) /
            ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2)
      (x := (1 : ℂ)) harg one_mem_slitPlane
  simpa [nearOneLogCorrection] using
    (tendsto_const_nhds.mul hlog :
      Tendsto
        (fun z : ℂ =>
          ((2 : ℂ) ^ (N + 1))⁻¹ *
            Complex.log
              ((1 : ℂ) +
                (c / z ^ (2 ^ (N + 1))) /
                  ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2))
        atInfinity (𝓝 (((2 : ℂ) ^ (N + 1))⁻¹ * 0)))

noncomputable def logCorrectionSeries (c : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, nearOneLogCorrection c n z

noncomputable def logCorrectionTail (c : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, nearOneLogCorrection c (n + 1) z

noncomputable def logSeriesBottcherRatio (c : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (logCorrectionSeries c z)

noncomputable def logSeriesBottcherApprox (c : ℂ) (z : ℂ) : ℂ :=
  z * logSeriesBottcherRatio c z

lemma logSeriesBottcherApprox_div (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    logSeriesBottcherApprox c z / z = logSeriesBottcherRatio c z := by
  calc
    logSeriesBottcherApprox c z / z =
        (z * logSeriesBottcherRatio c z) / z := by
      simp [logSeriesBottcherApprox]
    _ = logSeriesBottcherRatio c z := by
      field_simp [hz, mul_comm, mul_left_comm, mul_assoc]

def LogCorrectionSeriesMajorizedOnExterior (c : ℂ) (R : ℝ) : Prop :=
  ∃ u : ℕ → ℝ,
    Summable u ∧
      ∀ n z, z ∈ {z : ℂ | R < ‖z‖} →
        ‖nearOneLogCorrection c n z‖ ≤ u n

lemma nearOneLogCorrection_eq_simple
    (c : ℂ) (N : ℕ) (z : ℂ)
    (hz : z ≠ 0) (hA : (quadratic_map c)^[N] z ≠ 0) :
    nearOneLogCorrection c N z =
      ((2 : ℂ) ^ (N + 1))⁻¹ *
        Complex.log ((1 : ℂ) + c / (((quadratic_map c)^[N] z) ^ 2)) := by
  have hzpowN : z ^ (2 ^ N) ≠ 0 := pow_ne_zero _ hz
  have hApow : ((quadratic_map c)^[N] z) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hpow : z ^ (2 ^ (N + 1)) = (z ^ (2 ^ N)) ^ 2 := by
    simp [pow_mul, pow_succ]
  have hterm :
      (c / z ^ (2 ^ (N + 1))) /
          ((quadratic_map c)^[N] z / z ^ (2 ^ N)) ^ 2 =
        c / (((quadratic_map c)^[N] z) ^ 2) := by
    rw [hpow]
    field_simp [hzpowN, hApow]
  simp [nearOneLogCorrection, hterm]

lemma nearOneLogCorrection_quadratic_map_eq_two_mul_succ
    (c : ℂ) (N : ℕ) (z : ℂ)
    (hz : z ≠ 0)
    (hzq : quadratic_map c z ≠ 0)
    (hA : (quadratic_map c)^[N + 1] z ≠ 0) :
    nearOneLogCorrection c N (quadratic_map c z) =
      (2 : ℂ) * nearOneLogCorrection c (N + 1) z := by
  have hAleft : (quadratic_map c)^[N] (quadratic_map c z) ≠ 0 := by
    simpa [Function.iterate_succ_apply] using hA
  have hleft := nearOneLogCorrection_eq_simple c N (quadratic_map c z) hzq hAleft
  have hright := nearOneLogCorrection_eq_simple c (N + 1) z hz hA
  have hscalar :
      ((2 : ℂ) ^ (N + 1))⁻¹ =
        (2 : ℂ) * ((2 : ℂ) ^ (N + 2))⁻¹ := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hpow : (2 : ℂ) ^ (N + 2) = (2 : ℂ) * (2 : ℂ) ^ (N + 1) := by
      have hN : N + 2 = (N + 1) + 1 := by omega
      rw [hN, pow_succ]
      ring
    rw [hpow]
    field_simp [h2, pow_ne_zero (N + 1) h2]
  calc
    nearOneLogCorrection c N (quadratic_map c z)
        = ((2 : ℂ) ^ (N + 1))⁻¹ *
            Complex.log ((1 : ℂ) + c / (((quadratic_map c)^[N]
              (quadratic_map c z)) ^ 2)) := hleft
    _ = ((2 : ℂ) ^ (N + 1))⁻¹ *
            Complex.log ((1 : ℂ) + c / (((quadratic_map c)^[N + 1] z) ^ 2)) := by
          rw [Function.iterate_succ_apply]
    _ = (2 : ℂ) * (((2 : ℂ) ^ (N + 2))⁻¹ *
            Complex.log ((1 : ℂ) + c / (((quadratic_map c)^[N + 1] z) ^ 2))) := by
          rw [hscalar]
          ring
    _ = (2 : ℂ) * nearOneLogCorrection c (N + 1) z := by
          rw [hright]

noncomputable def exteriorGrowthLower : ℝ → ℕ → ℝ
  | R, 0 => R
  | R, n + 1 => (exteriorGrowthLower R n) ^ 2 / 2

lemma exteriorGrowthLower_nonneg {R : ℝ} (hR : 0 ≤ R) :
    ∀ n, 0 ≤ exteriorGrowthLower R n
  | 0 => hR
  | n + 1 => by
      exact div_nonneg (sq_nonneg _) (by norm_num)

lemma exteriorGrowthLower_le_norm_iterate
    (c z : ℂ) (R : ℝ)
    (hR0 : 0 ≤ R) (hRc : ‖c‖ + 2 ≤ R) (hR4 : 4 ≤ R)
    (hz : R ≤ ‖z‖) :
    ∀ n, exteriorGrowthLower R n ≤ ‖(quadratic_map c)^[n] z‖
  | 0 => by simpa [exteriorGrowthLower] using hz
  | n + 1 => by
      have ih : exteriorGrowthLower R n ≤ ‖(quadratic_map c)^[n] z‖ :=
        exteriorGrowthLower_le_norm_iterate c z R hR0 hRc hR4 hz n
      have hlower_nonneg : 0 ≤ exteriorGrowthLower R n :=
        exteriorGrowthLower_nonneg hR0 n
      have hzn_ge : R ≤ ‖(quadratic_map c)^[n] z‖ := by
        have hstart : ‖c‖ + 1 ≤ ‖z‖ := by linarith
        exact le_trans hz (iterate_quadratic_map_norm_ge c z n hstart)
      have hquad_lower :
          ‖quadratic_map c ((quadratic_map c)^[n] z)‖ ≥
            ‖(quadratic_map c)^[n] z‖ ^ 2 - ‖c‖ :=
        quadratic_map_norm_lower c ((quadratic_map c)^[n] z)
      have hhalf :
          ‖(quadratic_map c)^[n] z‖ ^ 2 / 2 ≤
            ‖(quadratic_map c)^[n] z‖ ^ 2 - ‖c‖ := by
        have hc_le : ‖c‖ ≤ ‖(quadratic_map c)^[n] z‖ ^ 2 / 2 := by
          have hn_ge_c2 : ‖c‖ + 2 ≤ ‖(quadratic_map c)^[n] z‖ :=
            le_trans hRc hzn_ge
          nlinarith [norm_nonneg c]
        nlinarith
      have hmono_sq :
          (exteriorGrowthLower R n) ^ 2 / 2 ≤
            ‖(quadratic_map c)^[n] z‖ ^ 2 / 2 := by
        nlinarith [ih, hlower_nonneg, norm_nonneg ((quadratic_map c)^[n] z)]
      calc
        exteriorGrowthLower R (n + 1)
            = (exteriorGrowthLower R n) ^ 2 / 2 := by
              simp [exteriorGrowthLower]
        _ ≤ ‖quadratic_map c ((quadratic_map c)^[n] z)‖ :=
          le_trans hmono_sq (le_trans hhalf hquad_lower)
        _ = ‖(quadratic_map c)^[n + 1] z‖ := by
              rw [Function.iterate_succ_apply']

lemma LogCorrectionSeriesMajorizedOnExterior.of_large_radius
    (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R) :
    LogCorrectionSeriesMajorizedOnExterior c R := by
  let u : ℕ → ℝ := fun n => ((3 : ℝ) / 2) * ‖c‖ * ((1 / 2 : ℝ) ^ (n + 1))
  have hgeom : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) :=
    summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hu : Summable u := by
    have hshift : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ (n + 1))) := by
      simpa [pow_succ'] using (hgeom.mul_left (1 / 2 : ℝ))
    exact hshift.mul_left (((3 : ℝ) / 2) * ‖c‖)
  refine ⟨u, hu, ?_⟩
  intro n z hz
  have hz_ge_c2 : ‖c‖ + 2 ≤ ‖z‖ := le_trans hR (le_of_lt hz)
  have hz_ne : z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    have : 0 < ‖z‖ := by linarith [norm_nonneg c]
    exact ne_of_gt this
  have hiter_ge_start : ‖z‖ ≤ ‖(quadratic_map c)^[n] z‖ :=
    iterate_quadratic_map_norm_ge c z n (by linarith)
  have hiter_ge_c2 : ‖c‖ + 2 ≤ ‖(quadratic_map c)^[n] z‖ :=
    le_trans hz_ge_c2 hiter_ge_start
  have hA_ne : (quadratic_map c)^[n] z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    have : 0 < ‖(quadratic_map c)^[n] z‖ := by linarith [norm_nonneg c]
    exact ne_of_gt this
  let w : ℂ := c / (((quadratic_map c)^[n] z) ^ 2)
  have hw_norm_le_c : ‖w‖ ≤ ‖c‖ := by
    have hden_norm_ge_one : 1 ≤ ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by
      have hbase : 1 ≤ ‖(quadratic_map c)^[n] z‖ := by linarith [norm_nonneg c]
      calc
        1 ≤ ‖(quadratic_map c)^[n] z‖ ^ 2 := by nlinarith
        _ = ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [norm_pow]
    have hden_pos : 0 < ‖(((quadratic_map c)^[n] z) ^ 2)‖ :=
      lt_of_lt_of_le zero_lt_one hden_norm_ge_one
    calc
      ‖w‖ = ‖c‖ / ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [w]
      _ ≤ ‖c‖ := div_le_self (norm_nonneg c) (by linarith)
  have hw_half : ‖w‖ ≤ (1 / 2 : ℝ) := by
    by_cases hc0 : ‖c‖ = 0
    · have : ‖w‖ = 0 := le_antisymm (by simpa [hc0] using hw_norm_le_c) (norm_nonneg _)
      nlinarith
    · have hc_pos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
      have hden_norm_ge : 2 * ‖c‖ ≤ ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by
        calc
          2 * ‖c‖ ≤ ‖(quadratic_map c)^[n] z‖ ^ 2 := by
            nlinarith [hiter_ge_c2, norm_nonneg c]
          _ = ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [norm_pow]
      have hden_pos : 0 < ‖(((quadratic_map c)^[n] z) ^ 2)‖ :=
        lt_of_lt_of_le (by nlinarith) hden_norm_ge
      rw [show ‖w‖ = ‖c‖ / ‖(((quadratic_map c)^[n] z) ^ 2)‖ by simp [w]]
      rw [div_le_iff₀ hden_pos]
      nlinarith
  have hlog_bound :
      ‖Complex.log ((1 : ℂ) + w)‖ ≤ ((3 : ℝ) / 2) * ‖w‖ :=
    Complex.norm_log_one_add_half_le_self hw_half
  have hsimple := nearOneLogCorrection_eq_simple c n z hz_ne hA_ne
  have hscalar_norm :
      ‖(((2 : ℂ) ^ (n + 1))⁻¹)‖ = (1 / 2 : ℝ) ^ (n + 1) := by
    simp [norm_inv, norm_pow]
  calc
    ‖nearOneLogCorrection c n z‖
        = ‖(((2 : ℂ) ^ (n + 1))⁻¹) *
            Complex.log ((1 : ℂ) + w)‖ := by simp [hsimple, w]
    _ = ((1 / 2 : ℝ) ^ (n + 1)) *
          ‖Complex.log ((1 : ℂ) + w)‖ := by simp [hscalar_norm]
    _ ≤ ((1 / 2 : ℝ) ^ (n + 1)) * (((3 : ℝ) / 2) * ‖w‖) := by
          exact mul_le_mul_of_nonneg_left hlog_bound (pow_nonneg (by norm_num) _)
    _ ≤ ((1 / 2 : ℝ) ^ (n + 1)) * (((3 : ℝ) / 2) * ‖c‖) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hw_norm_le_c (by norm_num))
            (pow_nonneg (by norm_num) _)
    _ = u n := by simp [u, mul_comm, mul_left_comm]

lemma summable_nearOneLogCorrection_of_large_radius
    (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R)
    {z : ℂ} (hz : R < ‖z‖) :
    Summable (fun n : ℕ => nearOneLogCorrection c n z) := by
  rcases LogCorrectionSeriesMajorizedOnExterior.of_large_radius (c := c) hR with
    ⟨u, hu, hbound⟩
  have hnorm : Summable (fun n : ℕ => ‖nearOneLogCorrection c n z‖) :=
    hu.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbound n z hz)
  exact hnorm.of_norm

lemma logCorrectionSeries_eq_zero_add_tail_of_large_radius
    (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R)
    {z : ℂ} (hz : R < ‖z‖) :
    logCorrectionSeries c z =
      nearOneLogCorrection c 0 z + logCorrectionTail c z := by
  have hsum := summable_nearOneLogCorrection_of_large_radius c hR hz
  exact Summable.tsum_eq_zero_add hsum

lemma logCorrectionSeries_quadratic_map_eq_two_mul_tail_of_large_radius
    (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R)
    {z : ℂ} (hz : R < ‖z‖) :
    logCorrectionSeries c (quadratic_map c z) =
      (2 : ℂ) * logCorrectionTail c z := by
  have hz_ge_c2 : ‖c‖ + 2 ≤ ‖z‖ := le_trans hR (le_of_lt hz)
  have hz_ne : z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    exact ne_of_gt (by linarith [norm_nonneg c])
  have hzq : quadratic_map c z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    have hqnorm := quadratic_map_norm_ge_add_one c z hz_ge_c2
    exact ne_of_gt (by linarith [norm_nonneg z])
  have hA : ∀ k : ℕ, (quadratic_map c)^[k + 1] z ≠ 0 := by
    intro k
    apply (norm_ne_zero_iff).1
    have hiter := iterate_quadratic_map_norm_ge c z (k + 1) (by linarith)
    exact ne_of_gt (by linarith [norm_nonneg z, norm_nonneg c])
  calc
    logCorrectionSeries c (quadratic_map c z)
        = ∑' n : ℕ, nearOneLogCorrection c n (quadratic_map c z) := rfl
    _ = ∑' n : ℕ, (2 : ℂ) * nearOneLogCorrection c (n + 1) z := by
          apply tsum_congr
          intro n
          exact nearOneLogCorrection_quadratic_map_eq_two_mul_succ c n z hz_ne hzq (hA n)
    _ = (2 : ℂ) * ∑' n : ℕ, nearOneLogCorrection c (n + 1) z := by
          rw [tsum_mul_left]
    _ = (2 : ℂ) * logCorrectionTail c z := rfl

lemma exp_two_mul_nearOneLogCorrection_zero_of_large_radius
    (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R)
    {z : ℂ} (hz : R < ‖z‖) :
    Complex.exp ((2 : ℂ) * nearOneLogCorrection c 0 z) =
      (1 : ℂ) + c / z ^ 2 := by
  have hz_ge_c2 : ‖c‖ + 2 ≤ ‖z‖ := le_trans hR (le_of_lt hz)
  have hz_ne : z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    exact ne_of_gt (by linarith [norm_nonneg c])
  have hterm_half : ‖c / z ^ 2‖ ≤ (1 / 2 : ℝ) := by
    by_cases hc0 : ‖c‖ = 0
    · have hc_zero : c = 0 := norm_eq_zero.mp hc0
      simp [hc_zero]
    · have hc_pos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
      have hden_ge : 2 * ‖c‖ ≤ ‖z ^ 2‖ := by
        calc
          2 * ‖c‖ ≤ ‖z‖ ^ 2 := by nlinarith [hz_ge_c2, norm_nonneg c]
          _ = ‖z ^ 2‖ := by simp [norm_pow]
      have hden_pos : 0 < ‖z ^ 2‖ := lt_of_lt_of_le (by nlinarith) hden_ge
      rw [norm_div, div_le_iff₀ hden_pos]
      nlinarith
  have hslit : (1 : ℂ) + c / z ^ 2 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one
      (lt_of_le_of_lt hterm_half (by norm_num))
  have hsimple := nearOneLogCorrection_eq_simple c 0 z hz_ne hz_ne
  have htwo :
      (2 : ℂ) * nearOneLogCorrection c 0 z =
        Complex.log ((1 : ℂ) + c / z ^ 2) := by
    have hsimple' :
        nearOneLogCorrection c 0 z =
          ((2 : ℂ) ^ 1)⁻¹ * Complex.log ((1 : ℂ) + c / z ^ 2) := by
      simpa using hsimple
    rw [hsimple']
    field_simp
  rw [htwo]
  exact Complex.exp_log (Complex.slitPlane_ne_zero hslit)

lemma logSeriesBottcherApprox_conj_of_large_radius
    (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R)
    {z : ℂ} (hz : R < ‖z‖) :
    logSeriesBottcherApprox c (quadratic_map c z) =
      (logSeriesBottcherApprox c z)^2 := by
  have hz_ge_c2 : ‖c‖ + 2 ≤ ‖z‖ := le_trans hR (le_of_lt hz)
  have hz_ne : z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    exact ne_of_gt (by linarith [norm_nonneg c])
  have htail := logCorrectionSeries_eq_zero_add_tail_of_large_radius c hR hz
  have hshift := logCorrectionSeries_quadratic_map_eq_two_mul_tail_of_large_radius c hR hz
  have hexp0 := exp_two_mul_nearOneLogCorrection_zero_of_large_radius c hR hz
  have hquad :
      quadratic_map c z = z ^ 2 * ((1 : ℂ) + c / z ^ 2) := by
    calc
      quadratic_map c z = z ^ 2 + c := by rfl
      _ = z ^ 2 * ((1 : ℂ) + c / z ^ 2) := by
        field_simp [hz_ne]
  calc
    logSeriesBottcherApprox c (quadratic_map c z)
        = quadratic_map c z * Complex.exp (logCorrectionSeries c (quadratic_map c z)) := by
          rfl
    _ = quadratic_map c z * Complex.exp ((2 : ℂ) * logCorrectionTail c z) := by
          rw [hshift]
    _ = (z ^ 2 * ((1 : ℂ) + c / z ^ 2)) *
          Complex.exp ((2 : ℂ) * logCorrectionTail c z) := by
          rw [hquad]
    _ = z ^ 2 * Complex.exp ((2 : ℂ) * logCorrectionSeries c z) := by
          rw [htail]
          rw [show (2 : ℂ) * (nearOneLogCorrection c 0 z + logCorrectionTail c z) =
              (2 : ℂ) * nearOneLogCorrection c 0 z + (2 : ℂ) * logCorrectionTail c z by ring]
          rw [Complex.exp_add, hexp0]
          ring
    _ = (z * Complex.exp (logCorrectionSeries c z)) ^ 2 := by
          rw [show (2 : ℂ) * logCorrectionSeries c z =
              logCorrectionSeries c z + logCorrectionSeries c z by ring]
          rw [Complex.exp_add]
          ring
    _ = (logSeriesBottcherApprox c z)^2 := by rfl

lemma nearOneLogCorrection_simple_arg_mem_slitPlane_of_large_radius
    (c : ℂ) (n : ℕ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R)
    {z : ℂ} (hz : R < ‖z‖) :
    (1 : ℂ) + c / (((quadratic_map c)^[n] z) ^ 2) ∈ Complex.slitPlane := by
  have hiter_ge_c2 : ‖c‖ + 2 ≤ ‖(quadratic_map c)^[n] z‖ :=
    le_trans (le_trans hR (le_of_lt hz))
      (iterate_quadratic_map_norm_ge c z n (by linarith))
  have hhalf : ‖c / (((quadratic_map c)^[n] z) ^ 2)‖ ≤ (1 / 2 : ℝ) := by
    by_cases hc0 : ‖c‖ = 0
    · have hc_zero : c = 0 := norm_eq_zero.mp hc0
      simp [hc_zero]
    · have hc_pos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
      have hden_ge : 2 * ‖c‖ ≤ ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by
        calc
          2 * ‖c‖ ≤ ‖(quadratic_map c)^[n] z‖ ^ 2 := by
            nlinarith [hiter_ge_c2, norm_nonneg c]
          _ = ‖(((quadratic_map c)^[n] z) ^ 2)‖ := by simp [norm_pow]
      have hden_pos : 0 < ‖(((quadratic_map c)^[n] z) ^ 2)‖ :=
        lt_of_lt_of_le (by nlinarith) hden_ge
      rw [norm_div, div_le_iff₀ hden_pos]
      nlinarith
  exact Complex.mem_slitPlane_of_norm_lt_one
    (lt_of_le_of_lt hhalf (by norm_num))

lemma nearOneLogCorrection_differentiableOn_large_radius
    (c : ℂ) (n : ℕ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R) :
    DifferentiableOn ℂ (nearOneLogCorrection c n) {z : ℂ | R < ‖z‖} := by
  let U : Set ℂ := {z : ℂ | R < ‖z‖}
  let A : ℂ → ℂ := fun z => (quadratic_map c)^[n] z
  let simple : ℂ → ℂ := fun z =>
    ((2 : ℂ) ^ (n + 1))⁻¹ *
      Complex.log ((1 : ℂ) + c / ((A z) ^ 2))
  have hA_diff : DifferentiableOn ℂ A U :=
    ((quadratic_map_differentiable c).iterate n).differentiableOn
  have hden_ne : ∀ z ∈ U, (A z) ^ 2 ≠ 0 := by
    intro z hz
    change R < ‖z‖ at hz
    have hiter_ge_start : ‖z‖ ≤ ‖A z‖ :=
      iterate_quadratic_map_norm_ge c z n (by
        have : ‖c‖ + 1 ≤ ‖z‖ := by linarith [hR, hz]
        exact this)
    have hpos : 0 < ‖A z‖ := lt_of_lt_of_le
      (by linarith [hR, hz, norm_nonneg c]) hiter_ge_start
    exact pow_ne_zero 2 ((norm_ne_zero_iff).1 (ne_of_gt hpos))
  have harg_diff :
      DifferentiableOn ℂ (fun z => (1 : ℂ) + c / ((A z) ^ 2)) U := by
    have hsq : DifferentiableOn ℂ (fun z => (A z) ^ 2) U := hA_diff.pow 2
    have hinv : DifferentiableOn ℂ (fun z => ((A z) ^ 2)⁻¹) U :=
      hsq.inv hden_ne
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hinv.const_mul c).const_add (1 : ℂ)
  have hlog_diff :
      DifferentiableOn ℂ (fun z => Complex.log ((1 : ℂ) + c / ((A z) ^ 2))) U := by
    refine harg_diff.clog ?_
    intro z hz
    exact nearOneLogCorrection_simple_arg_mem_slitPlane_of_large_radius c n hR hz
  have hsimple_diff : DifferentiableOn ℂ simple U := by
    simpa [simple] using hlog_diff.const_mul (((2 : ℂ) ^ (n + 1))⁻¹)
  refine hsimple_diff.congr ?_
  intro z hz
  change R < ‖z‖ at hz
  have hz_ne : z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    exact ne_of_gt (by linarith [hR, hz, norm_nonneg c])
  have hA_ne : A z ≠ 0 := by
    apply (norm_ne_zero_iff).1
    have hiter_ge_start : ‖z‖ ≤ ‖A z‖ :=
      iterate_quadratic_map_norm_ge c z n (by
        have : ‖c‖ + 1 ≤ ‖z‖ := by linarith [hR, hz]
        exact this)
    exact ne_of_gt (lt_of_lt_of_le
      (by linarith [hR, hz, norm_nonneg c]) hiter_ge_start)
  simpa [simple, A] using nearOneLogCorrection_eq_simple c n z hz_ne hA_ne

lemma logCorrectionSeries_differentiableOn_large_radius
      (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R) :
      DifferentiableOn ℂ (logCorrectionSeries c) {z : ℂ | R < ‖z‖} := by
  rcases LogCorrectionSeriesMajorizedOnExterior.of_large_radius (c := c) hR with
    ⟨u, hu, hbound⟩
  have hUopen : IsOpen ({z : ℂ | R < ‖z‖} : Set ℂ) :=
    isOpen_lt continuous_const continuous_norm
  exact differentiableOn_tsum_of_summable_norm
    (F := fun n z => nearOneLogCorrection c n z)
    (U := {z : ℂ | R < ‖z‖})
    hu
    (fun n => nearOneLogCorrection_differentiableOn_large_radius c n hR)
    hUopen
    hbound

lemma logSeriesBottcherRatio_differentiableOn_large_radius
      (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R) :
      DifferentiableOn ℂ (logSeriesBottcherRatio c) {z : ℂ | R < ‖z‖} := by
  simpa [logSeriesBottcherRatio] using
    (logCorrectionSeries_differentiableOn_large_radius c hR).cexp

lemma logSeriesBottcherApprox_differentiableOn_large_radius
      (c : ℂ) {R : ℝ} (hR : ‖c‖ + 2 ≤ R) :
      DifferentiableOn ℂ (logSeriesBottcherApprox c) {z : ℂ | R < ‖z‖} := by
  simpa [logSeriesBottcherApprox] using
    differentiableOn_id.mul (logSeriesBottcherRatio_differentiableOn_large_radius c hR)

lemma tendsto_logCorrectionSeries_atInfinity (c : ℂ) :
    Tendsto (logCorrectionSeries c) atInfinity (𝓝 (0 : ℂ)) := by
  rcases LogCorrectionSeriesMajorizedOnExterior.of_large_radius
      (c := c) (R := ‖c‖ + 2) le_rfl with ⟨u, hu, hbound⟩
  have hlarge : ∀ᶠ z in atInfinity, z ∈ {z : ℂ | ‖c‖ + 2 < ‖z‖} :=
    eventually_atInfinity_norm_gt (‖c‖ + 2)
  have hbound_eventually :
      ∀ᶠ z in atInfinity, ∀ n : ℕ, ‖nearOneLogCorrection c n z‖ ≤ u n := by
    filter_upwards [hlarge] with z hz n
    exact hbound n z hz
  have hterm :
      ∀ n : ℕ, Tendsto (fun z : ℂ => nearOneLogCorrection c n z)
        atInfinity (𝓝 (0 : ℂ)) :=
    fun n => tendsto_nearOneLogCorrection_atInfinity c n
  have htend :=
    tendsto_tsum_of_dominated_convergence
      (𝓕 := atInfinity)
      (f := fun z n => nearOneLogCorrection c n z)
      (g := fun _ : ℕ => (0 : ℂ))
      (bound := u)
      hu hterm hbound_eventually
  simpa [logCorrectionSeries] using htend

lemma tendsto_logSeriesBottcherRatio_atInfinity (c : ℂ) :
    Tendsto (logSeriesBottcherRatio c) atInfinity (𝓝 (1 : ℂ)) := by
  have hlog := tendsto_logCorrectionSeries_atInfinity c
  simpa [logSeriesBottcherRatio] using
    ((Complex.continuous_exp.tendsto (0 : ℂ)).comp hlog)

lemma tendsto_logSeriesBottcherApprox_div_atInfinity (c : ℂ) :
    Tendsto (fun z => logSeriesBottcherApprox c z / z) atInfinity (𝓝 (1 : ℂ)) := by
  have hratio := tendsto_logSeriesBottcherRatio_atInfinity c
  have hzne : ∀ᶠ z in atInfinity, z ≠ 0 :=
    (eventually_atInfinity_norm_gt 0).mono
      (fun _ hz => (norm_ne_zero_iff).1 (ne_of_gt hz))
  refine (tendsto_congr' ?_).2 hratio
  filter_upwards [hzne] with z hz
  exact logSeriesBottcherApprox_div c hz

lemma eventually_one_lt_norm_logSeriesBottcherApprox_atInfinity (c : ℂ) :
    ∀ᶠ z in atInfinity, 1 < ‖logSeriesBottcherApprox c z‖ := by
  have hratioNorm :
      Tendsto ((fun a : ℂ => ‖a‖) ∘
        (fun z : ℂ => logSeriesBottcherApprox c z / z)) atInfinity (𝓝 ‖(1 : ℂ)‖) :=
    (continuous_norm.tendsto (1 : ℂ)).comp
      (tendsto_logSeriesBottcherApprox_div_atInfinity c)
  have hratioHalf : ∀ᶠ z in atInfinity,
      (1 / 2 : ℝ) < ‖logSeriesBottcherApprox c z / z‖ := by
    have hball : Metric.ball (‖(1 : ℂ)‖) (1 / 2) ∈ 𝓝 ‖(1 : ℂ)‖ :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hratioNorm.eventually hball] with z hz
    have hzabs : |‖logSeriesBottcherApprox c z / z‖ - 1| < (1 / 2 : ℝ) := by
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using hz
    nlinarith [abs_lt.1 hzabs |>.1, abs_lt.1 hzabs |>.2]
  have hlarge : ∀ᶠ z in atInfinity, (2 : ℝ) < ‖z‖ :=
    eventually_atInfinity_norm_gt 2
  refine (hratioHalf.and hlarge).mono ?_
  intro z hz
  have hz_ne : z ≠ 0 := (norm_ne_zero_iff).1 (ne_of_gt (lt_trans (by norm_num) hz.2))
  have hprod : 1 < ‖logSeriesBottcherApprox c z / z‖ * ‖z‖ := by
    nlinarith [hz.1, hz.2]
  have hnorm :
      ‖logSeriesBottcherApprox c z / z‖ * ‖z‖ =
        ‖logSeriesBottcherApprox c z‖ := by
    rw [norm_div]
    field_simp [(norm_ne_zero_iff).2 hz_ne]
  rw [hnorm] at hprod
  exact hprod

lemma exists_radius_one_lt_norm_logSeriesBottcherApprox (c : ℂ) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → 1 < ‖logSeriesBottcherApprox c z‖ := by
  have h := eventually_one_lt_norm_logSeriesBottcherApprox_atInfinity c
  dsimp [atInfinity] at h
  rcases (Filter.eventually_atTop.1 ((Filter.eventually_comap).1 h)) with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro z hz
  exact hR ‖z‖ (le_of_lt hz) z rfl

lemma quadratic_map_iter_maps_outside_open (c : ℂ) {z : ℂ}
    (hz : ‖z‖ > ‖c‖ + 2) :
    ∀ n : ℕ, ‖(quadratic_map c)^[n] z‖ > ‖c‖ + 2
  | 0 => by simpa using hz
  | n + 1 => by
      have hn := quadratic_map_iter_maps_outside_open c hz n
      have hge :
          ‖quadratic_map c ((quadratic_map c)^[n] z)‖ ≥
            ‖(quadratic_map c)^[n] z‖ + 1 :=
        quadratic_map_norm_ge_add_one c _ (le_of_lt hn)
      rw [Function.iterate_succ_apply']
      linarith

lemma logSeriesBottcherApprox_conj_iterate_outside_open
    (c : ℂ) {z : ℂ} (hz : ‖z‖ > ‖c‖ + 2) :
    ∀ n : ℕ,
      logSeriesBottcherApprox c ((quadratic_map c)^[n] z) =
        (logSeriesBottcherApprox c z) ^ (2 ^ n)
  | 0 => by simp
  | n + 1 => by
      have hn_out := quadratic_map_iter_maps_outside_open c hz n
      calc
        logSeriesBottcherApprox c ((quadratic_map c)^[n + 1] z)
            = logSeriesBottcherApprox c (quadratic_map c ((quadratic_map c)^[n] z)) := by
                rw [Function.iterate_succ_apply']
        _ = (logSeriesBottcherApprox c ((quadratic_map c)^[n] z)) ^ 2 :=
          logSeriesBottcherApprox_conj_of_large_radius c (R := ‖c‖ + 2) le_rfl hn_out
        _ = ((logSeriesBottcherApprox c z) ^ (2 ^ n)) ^ 2 := by
          rw [logSeriesBottcherApprox_conj_iterate_outside_open c hz n]
        _ = (logSeriesBottcherApprox c z) ^ (2 ^ (n + 1)) := by
          simp [pow_mul, pow_succ]

lemma one_lt_norm_logSeriesBottcherApprox_of_outside_open
    (c : ℂ) {z : ℂ} (hz : ‖z‖ > ‖c‖ + 2) :
    1 < ‖logSeriesBottcherApprox c z‖ := by
  rcases exists_radius_one_lt_norm_logSeriesBottcherApprox c with ⟨Rext, hExt⟩
  have hescape : Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop :=
    iterate_quadratic_map_tendsto_infty c z (le_of_lt hz)
  rcases (Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hescape) (Rext + 1))) with ⟨N, hN⟩
  have hlarge : Rext < ‖(quadratic_map c)^[N] z‖ := by
    have hN' := hN N le_rfl
    linarith
  have hPhi_large := hExt ((quadratic_map c)^[N] z) hlarge
  have hconj := logSeriesBottcherApprox_conj_iterate_outside_open c hz N
  have hpow_gt : 1 < ‖logSeriesBottcherApprox c z‖ ^ (2 ^ N) := by
    simpa [hconj, norm_pow] using hPhi_large
  by_contra hnot
  have hle : ‖logSeriesBottcherApprox c z‖ ≤ 1 := le_of_not_gt hnot
  have hpow_le : ‖logSeriesBottcherApprox c z‖ ^ (2 ^ N) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hle
  linarith

end MLC
