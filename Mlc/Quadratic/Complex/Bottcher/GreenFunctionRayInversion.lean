import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.ParaPuzzleBasis
import Mathlib.Topology.Order.IntermediateValue

/-!
# Green Function Ray Inversion at `c = 2`

This file formalizes the construction of the external ray map as the inverse of
`bottcher_map 2` via the Green function.

## Definition

`bottcher_map 2 z = (z / ‖z‖) * exp(green_function 2 z)` (polar Green map).

The inverse `f` maps each `w` (with `‖w‖ > 1`) to the unique point `z` in the
basin of infinity satisfying:
- `arg(z) = arg(w)` (same direction)
- `green_function 2 z = Real.log ‖w‖` (matching Green function value)

## Plan status (Lemmas A–E)
- [x] Lemma A: `green_function_pos_on_outside_open` — follows from `green_function_pos_of_basin`.
- [x] Lemma B: `green_function_tendsto_atTop` — follows from `bounded_sublevel_green_function`.
- [x*] Lemma C: `green_function_strictMono_along_ray` — proved for the real ray (c=2, u=1);
       general complex-direction case remains sorry (requires harmonic analysis).
- [x*] Lemma D: `exists_ray_preimage_green` — existence proved via IVT; uniqueness sorry.
- [ ] Lemma E: `external_ray_map_two_constructive` — needs full Lemma C (sorry).
-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric Real

namespace GreenFunctionRayInversion

/-! ## Lemma A: Green function positivity on the outside-open set -/

/-- The outside-open set `{z : ‖z‖ > ‖c‖ + 2}` is contained in the basin of infinity. -/
lemma outside_open_subset_basin (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ Quadratic.basin_of_infinity c := by
  intro z hz
  have hz_disk : z ∈ outside_disk c :=
    (outside_open_subset_outside_disk c) hz
  exact outside_disk_subset_quadratic_basin c hz_disk

/-- **Lemma A**: The Green function is strictly positive on the outside-open set. -/
lemma green_function_pos_on_outside_open (c : ℂ) (z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    0 < Quadratic.green_function c z :=
  green_function_pos_of_basin c z (outside_open_subset_basin c hz)

/-! ## Lemma B: Green function diverges to +∞ as ‖z‖ → ∞ -/

/-- **Lemma B**: For any bound `r`, the Green function eventually exceeds `r` for large `‖z‖`.
This follows from the fact that sublevel sets are bounded. -/
lemma green_function_eventually_large (c : ℂ) (r : ℝ) :
    ∀ᶠ z : ℂ in atInfinity, r ≤ Quadratic.green_function c z := by
  have hbdd := bounded_sublevel_green_function c r
  rw [isBounded_iff_forall_norm_le] at hbdd
  obtain ⟨R, hR⟩ := hbdd
  have hnorm_gt : ∀ᶠ z : ℂ in atInfinity, R < ‖z‖ := eventually_atInfinity_norm_gt R
  refine hnorm_gt.mono fun z hz => ?_
  by_contra h
  push_neg at h
  have hmem : z ∈ {z : ℂ | Quadratic.green_function c z < r} := by simpa using h
  have hle : ‖z‖ ≤ R := hR z hmem
  linarith

/-- **Lemma B'**: The Green function tends to +∞ at infinity. -/
lemma green_function_tendsto_atTop (c : ℂ) :
    Tendsto (Quadratic.green_function c) atInfinity atTop := by
  rw [Filter.tendsto_atTop]
  intro r
  exact green_function_eventually_large c r

/-! ## Two-sided bound: G_c(z) ≈ log ‖z‖ uniformly on the outside-open set -/

/-- The Green function is bounded above by `log ‖z‖ + M` on the outside-open set.
Combined with `green_function_bdd_below_log`, this gives a uniform two-sided bound. -/
lemma green_function_bdd_above_log (c z : ℂ) (h : ‖z‖ > escape_bound c) :
    green_function c z ≤ Real.log ‖z‖ + (2 * ‖c‖ / (escape_bound c)^2) := by
  have h_dist := dist_potential_seq_green_function_le_of_escaping c z 0 h
  simp only [pow_zero, one_div_one, one_mul] at h_dist
  have h_pot0 : potential_seq c z 0 = Real.log ‖z‖ := by
    dsimp [potential_seq]
    rw [max_eq_right]
    · simp
    · have h_eb := escape_bound_ge_R c
      have h_R := R_ge_two c
      linarith
  rw [h_pot0, dist_comm, dist_eq_norm, Real.norm_eq_abs] at h_dist
  linarith [abs_le.mp h_dist]

/-! ## Orbit structure for real inputs under f_2 = z^2 + 2 -/

/-- The `f_2` iteration on ℝ: `f2 x = x^2 + 2`. -/
private noncomputable def f2 : ℝ → ℝ := fun x => x ^ 2 + 2

/-- All iterates of `f_2(x) = x^2 + 2` on a positive real input are positive. -/
private lemma f2_iterate_pos (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) : 0 < f2 ^[n] ρ := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, f2]
    positivity

/-- The `f_2` iterate is strictly monotone: ρ₁ < ρ₂ implies f2^[n] ρ₁ < f2^[n] ρ₂. -/
private lemma f2_iterate_strictMono {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂) (hρ₁ : 0 < ρ₁) (n : ℕ) :
    f2 ^[n] ρ₁ < f2 ^[n] ρ₂ := by
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, f2]
    nlinarith [f2_iterate_pos ρ₁ hρ₁ n, f2_iterate_pos ρ₂ (hρ₁.trans h) n, ih]

/-- The orbit of a coerced real `↑ρ : ℂ` under `fc 2 z = z^2 + 2` equals the
coercion of the real iterate `f2^[n] ρ`. -/
lemma orbit_two_ofReal (ρ : ℝ) (n : ℕ) :
    orbit (2 : ℂ) (↑ρ : ℂ) n = ↑(f2 ^[n] ρ) := by
  induction n with
  | zero => simp [orbit_zero]
  | succ n ih =>
    simp only [orbit_succ, fc, ih, Function.iterate_succ', Function.comp, f2]
    push_cast
    ring

/-- For a positive real `ρ`, the norm of the orbit equals the real iterate `f2^[n] ρ`. -/
lemma norm_orbit_two_real (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ‖orbit (2 : ℂ) (↑ρ : ℂ) n‖ = f2 ^[n] ρ := by
  rw [orbit_two_ofReal, Complex.norm_real]
  exact Real.norm_of_nonneg (f2_iterate_pos ρ hρ n).le

/-- The `f_2` iterate grows without bound if started above 4:
`f2^[n] ρ ≥ ρ > 4` (in fact it grows super-exponentially). -/
private lemma f2_iterate_ge (ρ : ℝ) (hρ : ρ > 4) (n : ℕ) : f2 ^[n] ρ ≥ ρ := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp, f2]
    nlinarith [sq_nonneg (f2 ^[n] ρ - ρ)]

/-! ## Green function iteration along orbits -/

/-- The Green function satisfies `G_c(orbit c z n) = 2^n * G_c(z)`. -/
lemma green_function_orbit_eq (c z : ℂ) (n : ℕ) :
    green_function c (orbit c z n) = 2 ^ n * green_function c z := by
  induction n with
  | zero => simp [orbit_zero]
  | succ n ih =>
    rw [orbit_succ, green_function_functional_eq, ih]
    ring

/-! ## Orbit norm comparison for complex inputs at c = 2 -/

/-- For c = 2, the map f_2(z) = z² + 2 satisfies |f_2(z)| ≥ |z|² - 2. -/
private lemma norm_fc_two_ge (z : ℂ) : ‖fc (2 : ℂ) z‖ ≥ ‖z‖^2 - 2 := by
  have h := norm_fc_ge_norm_sq_sub_norm_c (2 : ℂ) z
  simp only [Complex.norm_two] at h
  exact h

/-- For c = 2 and |z| > 2, one iteration satisfies |f_2(z)| > |z|. -/
private lemma norm_fc_two_gt_of_gt_two (z : ℂ) (hz : ‖z‖ > 2) : ‖fc (2 : ℂ) z‖ > ‖z‖ := by
  have h := norm_fc_two_ge z
  have hnorm_pos : 0 < ‖z‖ := by linarith
  -- |f_2(z)| ≥ |z|² - 2 = |z|(|z| - 2/|z|) > |z| when |z| > 2
  have hkey : ‖z‖^2 - 2 > ‖z‖ := by nlinarith [sq_pos_of_pos hnorm_pos]
  linarith

/-- For c = 2 and |z| > 4, the orbit norm stays above 4 and grows. -/
private lemma norm_orbit_two_gt_four (z : ℂ) (hz : ‖z‖ > 4) (n : ℕ) : ‖orbit (2 : ℂ) z n‖ > 4 := by
  induction n with
  | zero => simpa [orbit_zero]
  | succ n ih =>
    rw [orbit_succ]
    have h1 : ‖orbit (2 : ℂ) z n‖ > 2 := by linarith
    have h2 := norm_fc_two_gt_of_gt_two (orbit (2 : ℂ) z n) h1
    linarith

/-- For c = 2 and |z| > 4, the orbit norm is at least |z|. -/
private lemma norm_orbit_two_ge_norm (z : ℂ) (hz : ‖z‖ > 4) (n : ℕ) : ‖orbit (2 : ℂ) z n‖ ≥ ‖z‖ := by
  induction n with
  | zero => simp [orbit_zero]
  | succ n ih =>
    rw [orbit_succ]
    have h_n_gt_2 : ‖orbit (2 : ℂ) z n‖ > 2 := by linarith [norm_orbit_two_gt_four z hz n]
    have h := norm_fc_two_gt_of_gt_two (orbit (2 : ℂ) z n) h_n_gt_2
    linarith

/-- For c = 2, the norm after one iteration satisfies |f_2(z)| ≤ |z|² + 2. -/
private lemma norm_fc_two_le (z : ℂ) : ‖fc (2 : ℂ) z‖ ≤ ‖z‖^2 + 2 := by
  have h : ‖fc (2 : ℂ) z‖ = ‖z^2 + (2:ℂ)‖ := rfl
  calc ‖z^2 + (2:ℂ)‖ ≤ ‖z^2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
    _ = ‖z‖^2 + 2 := by rw [norm_sq, Complex.norm_two]

/-- For c = 2 and |z| > 4, log |f_2(z)| ≥ 2 * log |z| - log 2. -/
private lemma log_norm_fc_two_lower (z : ℂ) (hz : ‖z‖ > 4) :
    Real.log ‖fc (2 : ℂ) z‖ ≥ 2 * Real.log ‖z‖ - Real.log 2 := by
  have hz_pos : 0 < ‖z‖ := by linarith
  have hz_sq_pos : 0 < ‖z‖^2 := sq_pos_of_pos hz_pos
  have h1 := norm_fc_two_ge z
  have hfc_pos : 0 < ‖fc (2 : ℂ) z‖ := by
    have hsq : ‖z‖^2 > 16 := by nlinarith
    linarith
  have h2 : ‖z‖^2 - 2 ≥ ‖z‖^2 / 2 := by nlinarith
  have hsq_sub_pos : 0 < ‖z‖^2 - 2 := by nlinarith
  have hdiv_pos : 0 < ‖z‖^2 / 2 := by positivity
  have hlog_sq : Real.log (‖z‖^2) = 2 * Real.log ‖z‖ := by
    rw [sq, Real.log_mul hz_pos.ne' hz_pos.ne']; ring
  calc Real.log ‖fc (2 : ℂ) z‖ ≥ Real.log (‖z‖^2 - 2) := by
         apply Real.log_le_log hsq_sub_pos; linarith
    _ ≥ Real.log (‖z‖^2 / 2) := by
         apply Real.log_le_log hdiv_pos h2
    _ = Real.log (‖z‖^2) - Real.log 2 := by
         rw [Real.log_div (by positivity) (by norm_num)]
    _ = 2 * Real.log ‖z‖ - Real.log 2 := by rw [hlog_sq]

/-- For c = 2 and |z| > 4, log |f_2(z)| ≤ 2 * log |z| + log 2. -/
private lemma log_norm_fc_two_upper (z : ℂ) (hz : ‖z‖ > 4) :
    Real.log ‖fc (2 : ℂ) z‖ ≤ 2 * Real.log ‖z‖ + Real.log 2 := by
  have hz_pos : 0 < ‖z‖ := by linarith
  have hz_sq_pos : 0 < ‖z‖^2 := sq_pos_of_pos hz_pos
  have h1 := norm_fc_two_ge z
  have hfc_pos : 0 < ‖fc (2 : ℂ) z‖ := by
    have hsq : ‖z‖^2 > 16 := by nlinarith
    linarith
  have hle := norm_fc_two_le z
  have h2 : ‖z‖^2 + 2 ≤ 2 * ‖z‖^2 := by nlinarith
  have hadd_pos : 0 < ‖z‖^2 + 2 := by linarith
  have hlog_sq : Real.log (‖z‖^2) = 2 * Real.log ‖z‖ := by
    rw [sq, Real.log_mul hz_pos.ne' hz_pos.ne']; ring
  calc Real.log ‖fc (2 : ℂ) z‖ ≤ Real.log (‖z‖^2 + 2) := by
         apply Real.log_le_log hfc_pos hle
    _ ≤ Real.log (2 * ‖z‖^2) := by
         apply Real.log_le_log hadd_pos h2
    _ = Real.log 2 + Real.log (‖z‖^2) := by
         rw [Real.log_mul (by norm_num) (by positivity)]
    _ = Real.log 2 + 2 * Real.log ‖z‖ := by rw [hlog_sq]
    _ = 2 * Real.log ‖z‖ + Real.log 2 := by ring

/-- The log-norm of orbit n grows roughly like 2^n * log |z₀| with bounded error.
More precisely: log |orbit z n| ≥ 2^n * log |z| - (2^{n+1} - 2) * log 2 when |z| > 4. -/
private lemma log_norm_orbit_lower (z : ℂ) (hz : ‖z‖ > 4) (n : ℕ) :
    Real.log ‖orbit (2 : ℂ) z n‖ ≥ 2^n * Real.log ‖z‖ - (2^(n+1) - 2) * Real.log 2 := by
  induction n with
  | zero =>
    simp only [orbit_zero, pow_zero, one_mul]
    norm_num
  | succ n ih =>
    have h_orb_gt_4 : ‖orbit (2 : ℂ) z n‖ > 4 := norm_orbit_two_gt_four z hz n
    simp only [orbit_succ]
    have hstep := log_norm_fc_two_lower (orbit (2 : ℂ) z n) h_orb_gt_4
    calc Real.log ‖fc (2 : ℂ) (orbit (2 : ℂ) z n)‖
        ≥ 2 * Real.log ‖orbit (2 : ℂ) z n‖ - Real.log 2 := hstep
      _ ≥ 2 * (2^n * Real.log ‖z‖ - (2^(n+1) - 2) * Real.log 2) - Real.log 2 := by linarith
      _ = 2^(n+1) * Real.log ‖z‖ - (2 * (2^(n+1) - 2) + 1) * Real.log 2 := by ring
      _ = 2^(n+1) * Real.log ‖z‖ - (2^(n+2) - 3) * Real.log 2 := by ring
      _ ≥ 2^(n+1) * Real.log ‖z‖ - (2^(n+2) - 2) * Real.log 2 := by
          have hlog2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
          linarith

/-- Upper bound: log |orbit z n| ≤ 2^n * log |z| + (2^{n+1} - 2) * log 2 when |z| > 4. -/
private lemma log_norm_orbit_upper (z : ℂ) (hz : ‖z‖ > 4) (n : ℕ) :
    Real.log ‖orbit (2 : ℂ) z n‖ ≤ 2^n * Real.log ‖z‖ + (2^(n+1) - 2) * Real.log 2 := by
  induction n with
  | zero =>
    simp only [orbit_zero, pow_zero, one_mul]
    norm_num
  | succ n ih =>
    have h_orb_gt_4 : ‖orbit (2 : ℂ) z n‖ > 4 := norm_orbit_two_gt_four z hz n
    simp only [orbit_succ]
    have hstep := log_norm_fc_two_upper (orbit (2 : ℂ) z n) h_orb_gt_4
    calc Real.log ‖fc (2 : ℂ) (orbit (2 : ℂ) z n)‖
        ≤ 2 * Real.log ‖orbit (2 : ℂ) z n‖ + Real.log 2 := hstep
      _ ≤ 2 * (2^n * Real.log ‖z‖ + (2^(n+1) - 2) * Real.log 2) + Real.log 2 := by linarith
      _ = 2^(n+1) * Real.log ‖z‖ + (2 * (2^(n+1) - 2) + 1) * Real.log 2 := by ring
      _ = 2^(n+1) * Real.log ‖z‖ + (2^(n+2) - 3) * Real.log 2 := by ring
      _ ≤ 2^(n+1) * Real.log ‖z‖ + (2^(n+2) - 2) * Real.log 2 := by
          have hlog2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
          linarith

/-- For c = 2, log ‖orbit 2 z n‖ = 2^n * G_2(z) + bounded error.
More precisely, |log ‖orbit 2 z n‖ - 2^n * G_2(z)| ≤ M for all n when ‖z‖ > 4. -/
lemma log_norm_orbit_two_eq_green_scaled (z : ℂ) (hz : ‖z‖ > 4) (n : ℕ) :
    |Real.log ‖orbit (2 : ℂ) z n‖ - 2^n * green_function (2 : ℂ) z| ≤
    2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ))^2 := by
  -- From green_function_orbit_eq: G_2(orbit 2 z n) = 2^n * G_2(z)
  have hG : green_function (2 : ℂ) (orbit (2 : ℂ) z n) = 2^n * green_function (2 : ℂ) z :=
    green_function_orbit_eq (2 : ℂ) z n
  -- Need to show orbit norm stays above escape_bound
  have hesc_two : escape_bound (2 : ℂ) = 3 := by
    have h2norm : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast, norm_real,
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [escape_bound_eq_max, h2norm]; norm_num
  have horb_gt : ‖orbit (2 : ℂ) z n‖ > escape_bound (2 : ℂ) := by
    have h := norm_orbit_two_ge_norm z hz n
    rw [hesc_two]
    linarith
  -- Two-sided bound gives |G_2(orbit 2 z n) - log ‖orbit 2 z n‖| ≤ M
  have hbdd_lo := green_function_bdd_below_log (2 : ℂ) (orbit (2 : ℂ) z n) horb_gt
  have hbdd_hi := green_function_bdd_above_log (2 : ℂ) (orbit (2 : ℂ) z n) horb_gt
  rw [hG] at hbdd_lo hbdd_hi
  rw [abs_le]
  constructor <;> linarith

/-
NOTE: The following lemma was DELETED because its premise is FALSE.
For ARBITRARY z₁, z₂ with ‖z₂‖ > ‖z₁‖ > 4, the orbit log-ratio does NOT necessarily
tend to infinity. Counterexample: z₁ = 5, z₂ = 5.01*I gives |fc(z₂)| < |fc(z₁)|.

The correct version restricts to points on the SAME RAY: z₁ = t₁*u, z₂ = t₂*u.
See OrbitNormRatio.norm_orbit_two_ratio_tendsto_atTop_along_ray for the correct statement.
-/



/-! ## Lemma C: Strict monotonicity along the positive real ray for `c = 2` -/

/-- The orbit ratio of two positive reals grows: for ρ₁ < ρ₂ both > 4, the relative gap
`(f2^[n] ρ₂ - f2^[n] ρ₁) / f2^[n] ρ₁` grows at least geometrically with ratio 16/9.

Proof: δ_{n+1} = (A_n + B_n)*δ_n, and A_n^2/(A_n^2+2) ≥ 16/18 for A_n ≥ 4, so
ε_{n+1} = δ_{n+1}/A_{n+1} ≥ (16/9)*ε_n. -/
private lemma f2_relative_gap_grows {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂) (hρ₁ : ρ₁ > 4) (n : ℕ) :
    (f2 ^[n] ρ₂ - f2 ^[n] ρ₁) / f2 ^[n] ρ₁ ≥ (16 / 9) ^ n * ((ρ₂ - ρ₁) / ρ₁) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hρ₁pos : 0 < ρ₁ := by linarith
    have hA_ge : f2 ^[n] ρ₁ > 4 := lt_of_lt_of_le hρ₁ (f2_iterate_ge ρ₁ hρ₁ n)
    have hApos : 0 < f2 ^[n] ρ₁ := by linarith
    have hBgtA : f2 ^[n] ρ₁ < f2 ^[n] ρ₂ := f2_iterate_strictMono h hρ₁pos n
    have hA2pos : 0 < f2 ^[n] ρ₁ ^ 2 + 2 := by positivity
    -- Key step: new gap / new base ≥ (16/9) * old gap / old base
    have hstep : (f2 (f2 ^[n] ρ₂) - f2 (f2 ^[n] ρ₁)) / f2 (f2 ^[n] ρ₁) ≥
        (16 / 9) * ((f2 ^[n] ρ₂ - f2 ^[n] ρ₁) / f2 ^[n] ρ₁) := by
      simp only [f2]
      rw [ge_iff_le, ← sub_nonneg]
      have heq : (f2 ^[n] ρ₂ ^ 2 + 2 - (f2 ^[n] ρ₁ ^ 2 + 2)) / (f2 ^[n] ρ₁ ^ 2 + 2) -
          (16 / 9) * ((f2 ^[n] ρ₂ - f2 ^[n] ρ₁) / f2 ^[n] ρ₁) =
          (f2 ^[n] ρ₂ - f2 ^[n] ρ₁) *
          ((f2 ^[n] ρ₂ + f2 ^[n] ρ₁) * f2 ^[n] ρ₁ - (16 / 9) * (f2 ^[n] ρ₁ ^ 2 + 2)) /
          (f2 ^[n] ρ₁ * (f2 ^[n] ρ₁ ^ 2 + 2)) := by field_simp; ring
      rw [heq]
      apply div_nonneg
      · apply mul_nonneg (by linarith)
        nlinarith [mul_nonneg (show (0:ℝ) ≤ f2 ^[n] ρ₂ - f2 ^[n] ρ₁ by linarith) hApos.le,
                   mul_pos (show (0:ℝ) < f2 ^[n] ρ₁ - 4 by linarith) hApos]
      · exact mul_nonneg hApos.le hA2pos.le
    -- Chain the inductive step
    simp only [Function.iterate_succ', Function.comp, pow_succ]
    calc (f2 (f2 ^[n] ρ₂) - f2 (f2 ^[n] ρ₁)) / f2 (f2 ^[n] ρ₁)
        ≥ (16 / 9) * ((f2 ^[n] ρ₂ - f2 ^[n] ρ₁) / f2 ^[n] ρ₁) := hstep
      _ ≥ (16 / 9) * ((16 / 9) ^ n * ((ρ₂ - ρ₁) / ρ₁)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (16 / 9) ^ n * (16 / 9) * ((ρ₂ - ρ₁) / ρ₁) := by ring

/-- The orbit ratio `f2^[n] ρ₂ / f2^[n] ρ₁` tends to infinity when ρ₁ < ρ₂. -/
private lemma f2_ratio_tendsto_atTop {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂) (hρ₁ : ρ₁ > 4) :
    Tendsto (fun n : ℕ => f2 ^[n] ρ₂ / f2 ^[n] ρ₁) atTop atTop := by
  have hρ₁pos : 0 < ρ₁ := by linarith
  have hε₀pos : 0 < (ρ₂ - ρ₁) / ρ₁ := div_pos (by linarith) hρ₁pos
  -- Lower bound: ratio ≥ (16/9)^n * ε₀ (since ratio ≥ gap/base ≥ (16/9)^n * ε₀)
  have hbound : ∀ n : ℕ, (16 / 9 : ℝ) ^ n * ((ρ₂ - ρ₁) / ρ₁) ≤ f2 ^[n] ρ₂ / f2 ^[n] ρ₁ :=
    fun n => by
      have hgap := f2_relative_gap_grows h hρ₁ n
      have hApos := f2_iterate_pos ρ₁ hρ₁pos n
      -- f2^n ρ₂ / f2^n ρ₁ = (f2^n ρ₂ - f2^n ρ₁) / f2^n ρ₁ + 1 ≥ gap + 0 ≥ (16/9)^n * ε₀
      have hgap2 : f2 ^[n] ρ₂ / f2 ^[n] ρ₁ = (f2 ^[n] ρ₂ - f2 ^[n] ρ₁) / f2 ^[n] ρ₁ + 1 := by
        field_simp [hApos.ne']; ring
      linarith [hgap, hgap2.symm.le]
  -- (16/9)^n * ε₀ → ∞, so ratio → ∞ by monotone comparison
  apply tendsto_atTop_mono hbound
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 16/9)))
     (b / ((ρ₂ - ρ₁) / ρ₁)))
  exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
    have h1 := hN n hn
    calc b = b / ((ρ₂ - ρ₁) / ρ₁) * ((ρ₂ - ρ₁) / ρ₁) :=
              (div_mul_cancel₀ _ hε₀pos.ne').symm
      _ ≤ (16 / 9 : ℝ) ^ n * ((ρ₂ - ρ₁) / ρ₁) :=
              mul_le_mul_of_nonneg_right h1 hε₀pos.le⟩

/-- **Lemma C (real case)**: For `c = 2` and the positive real direction `u = 1`,
the Green function is strictly increasing: `ρ₁ < ρ₂` implies `G_2(ρ₁) < G_2(ρ₂)`.

Proof outline (by contradiction):
1. If G₂(ρ₁) ≥ G₂(ρ₂), then by the functional equation G₂(f2^n(ρᵢ)) = 2^n * G₂(ρᵢ).
2. The two-sided bound |G₂(z) - log‖z‖| ≤ M gives log(f2^n ρ₂/f2^n ρ₁) ≤ 2M + |t₁-t₂|.
3. So f2^n ρ₂/f2^n ρ₁ ≤ exp(2M + |t₁-t₂|), i.e., the ratio is BOUNDED.
4. But from `f2_ratio_tendsto_atTop`, the ratio → ∞. Contradiction. -/
lemma green_function_strictMono_along_real_ray_two {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂)
    (hρ₁ : ρ₁ > 4) :
    green_function (2 : ℂ) (↑ρ₁ : ℂ) < green_function (2 : ℂ) (↑ρ₂ : ℂ) := by
  by_contra hle
  push_neg at hle
  have hρ₁pos : 0 < ρ₁ := by linarith
  have hρ₂pos : 0 < ρ₂ := hρ₁pos.trans h
  set t₁ := green_function (2 : ℂ) (↑ρ₁ : ℂ)
  set t₂ := green_function (2 : ℂ) (↑ρ₂ : ℂ)
  set M := 2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ)) ^ 2
  -- escape_bound (2:ℂ) = max 2 (1 + ‖2‖) = max 2 3 = 3
  have hesc_two : escape_bound (2 : ℂ) = 3 := by
    have h2norm : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast, norm_real,
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [escape_bound_eq_max, h2norm]; norm_num
  -- All iterates of ρ₁ and ρ₂ stay above escape_bound
  have hesc₁ : ∀ n, ‖orbit (2 : ℂ) ↑ρ₁ n‖ > escape_bound (2 : ℂ) := fun n => by
    rw [norm_orbit_two_real ρ₁ hρ₁pos n, hesc_two]
    linarith [f2_iterate_ge ρ₁ hρ₁ n]
  have hesc₂ : ∀ n, ‖orbit (2 : ℂ) ↑ρ₂ n‖ > escape_bound (2 : ℂ) := fun n => by
    rw [norm_orbit_two_real ρ₂ hρ₂pos n, hesc_two]
    linarith [f2_iterate_ge ρ₂ (by linarith) n]
  -- The log-ratio log(f2^n ρ₂) - log(f2^n ρ₁) is bounded by 2M + |t₁-t₂|
  have hlog_bound : ∀ n, Real.log (f2 ^[n] ρ₂) - Real.log (f2 ^[n] ρ₁) ≤ 2 * M + |t₁ - t₂| := by
    intro n
    have hA := f2_iterate_pos ρ₁ hρ₁pos n
    have hB := f2_iterate_pos ρ₂ hρ₂pos n
    have hgorb₁ := green_function_orbit_eq (2 : ℂ) ↑ρ₁ n
    have hgorb₂ := green_function_orbit_eq (2 : ℂ) ↑ρ₂ n
    -- Upper: log(B_n) ≤ 2^n*t₂ + M  (G ≥ log - M, and G = 2^n*t₂)
    have hub₂ : Real.log (f2 ^[n] ρ₂) ≤ 2 ^ n * t₂ + M := by
      have hbdd := green_function_bdd_below_log (2 : ℂ) (orbit (2 : ℂ) ↑ρ₂ n) (hesc₂ n)
      simp only [norm_orbit_two_real ρ₂ hρ₂pos n] at hbdd
      linarith [hgorb₂]
    -- Lower: log(A_n) ≥ 2^n*t₁ - M  (G ≤ log + M, and G = 2^n*t₁)
    have hlb₁ : Real.log (f2 ^[n] ρ₁) ≥ 2 ^ n * t₁ - M := by
      have hbdd := green_function_bdd_above_log (2 : ℂ) (orbit (2 : ℂ) ↑ρ₁ n) (hesc₁ n)
      simp only [norm_orbit_two_real ρ₁ hρ₁pos n] at hbdd
      linarith [hgorb₁]
    -- Since hle: t₂ ≤ t₁, we have 2^n*(t₂-t₁) ≤ 0 ≤ |t₁-t₂|
    have h2n_bound : (2 : ℝ) ^ n * (t₂ - t₁) ≤ |t₁ - t₂| :=
      le_trans (mul_nonpos_of_nonneg_of_nonpos (pow_pos two_pos n).le (by linarith))
               (abs_nonneg _)
    linarith
  -- The log-ratio → ∞ (since the ratio → ∞ and log is monotone)
  have hratio_top := f2_ratio_tendsto_atTop h hρ₁
  have hlog_top : Tendsto (fun n => Real.log (f2 ^[n] ρ₂ / f2 ^[n] ρ₁)) atTop atTop :=
    Real.tendsto_log_atTop.comp hratio_top
  -- Extract N where the log-ratio exceeds the upper bound — contradiction
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp hlog_top) (2 * M + |t₁ - t₂| + 1))
  have hlog_N := hlog_bound N
  have hA_N := f2_iterate_pos ρ₁ hρ₁pos N
  have hB_N := f2_iterate_pos ρ₂ hρ₂pos N
  have hN' := hN N le_rfl
  rw [Real.log_div (by linarith) (by linarith)] at hN'
  linarith

/-- **Lemma C (complex rays, c = 2)**: For c = 2 and any unit direction u, strict monotonicity
holds along the ray. Proof follows the same pattern as the real case, using orbit norm bounds. -/
lemma green_function_strictMono_along_ray_two (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₁ < t₂) :
    green_function (2 : ℂ) (↑t₁ * u) < green_function (2 : ℂ) (↑t₂ * u) := by
  by_contra hle
  push_neg at hle
  have ht₁pos : 0 < t₁ := by linarith
  have ht₂pos : 0 < t₂ := ht₁pos.trans ht₂
  set z₁ := (t₁ : ℂ) * u
  set z₂ := (t₂ : ℂ) * u
  set g₁ := green_function (2 : ℂ) z₁
  set g₂ := green_function (2 : ℂ) z₂
  set M := 2 * ‖(2 : ℂ)‖ / (escape_bound (2 : ℂ)) ^ 2
  -- Norm identities
  have hnorm₁ : ‖z₁‖ = t₁ := by
    simp only [z₁, norm_mul, hu, mul_one, norm_real, Real.norm_of_nonneg ht₁pos.le]
  have hnorm₂ : ‖z₂‖ = t₂ := by
    simp only [z₂, norm_mul, hu, mul_one, norm_real, Real.norm_of_nonneg ht₂pos.le]
  -- escape_bound (2:ℂ) = 3
  have hesc_two : escape_bound (2 : ℂ) = 3 := by
    have h2norm : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast, norm_real,
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [escape_bound_eq_max, h2norm]; norm_num
  -- Both starting points are in the basin (norm > escape_bound)
  have hesc₁ : ‖z₁‖ > escape_bound (2 : ℂ) := by rw [hnorm₁, hesc_two]; linarith
  have hesc₂ : ‖z₂‖ > escape_bound (2 : ℂ) := by rw [hnorm₂, hesc_two]; linarith
  have hz₁_gt_4 : ‖z₁‖ > 4 := by rw [hnorm₁]; exact ht₁
  have hz₂_gt_4 : ‖z₂‖ > 4 := by rw [hnorm₂]; linarith
  -- Orbit norms stay above escape_bound
  have hesc_orb₁ : ∀ n, ‖orbit (2 : ℂ) z₁ n‖ > escape_bound (2 : ℂ) := fun n => by
    rw [hesc_two]
    have h := norm_orbit_two_ge_norm z₁ hz₁_gt_4 n
    linarith
  have hesc_orb₂ : ∀ n, ‖orbit (2 : ℂ) z₂ n‖ > escape_bound (2 : ℂ) := fun n => by
    rw [hesc_two]
    have h := norm_orbit_two_ge_norm z₂ hz₂_gt_4 n
    linarith
  -- By two-sided bound and functional equation, log-norm ratio is bounded
  have hlog_bound : ∀ n, Real.log ‖orbit (2 : ℂ) z₂ n‖ - Real.log ‖orbit (2 : ℂ) z₁ n‖ ≤
      2 * M + |g₁ - g₂| := fun n => by
    have hgorb₁ := green_function_orbit_eq (2 : ℂ) z₁ n
    have hgorb₂ := green_function_orbit_eq (2 : ℂ) z₂ n
    -- Upper bound on log ‖orbit z₂ n‖
    have hub₂ : Real.log ‖orbit (2 : ℂ) z₂ n‖ ≤ 2 ^ n * g₂ + M := by
      have hbdd := green_function_bdd_below_log (2 : ℂ) (orbit (2 : ℂ) z₂ n) (hesc_orb₂ n)
      linarith [hgorb₂]
    -- Lower bound on log ‖orbit z₁ n‖
    have hlb₁ : Real.log ‖orbit (2 : ℂ) z₁ n‖ ≥ 2 ^ n * g₁ - M := by
      have hbdd := green_function_bdd_above_log (2 : ℂ) (orbit (2 : ℂ) z₁ n) (hesc_orb₁ n)
      linarith [hgorb₁]
    -- Since hle: g₂ ≤ g₁, we have 2^n*(g₂-g₁) ≤ 0 ≤ |g₁-g₂|
    have h2n_bound : (2 : ℝ) ^ n * (g₂ - g₁) ≤ |g₁ - g₂| :=
      le_trans (mul_nonpos_of_nonneg_of_nonpos (pow_pos two_pos n).le (by linarith))
               (abs_nonneg _)
    linarith
  -- But by the two-sided bound at the starting points, log-norm ratio at n=0 is positive
  -- and should grow under iteration (roughly doubling each step for large norms)
  --
  -- For the real case, we used f2_ratio_tendsto_atTop to show the ratio → ∞.
  -- For the complex case, we need an analogous result, or use the fact that
  -- the log-norms approximately double, so log-ratio approximately doubles.
  --
  -- Key: log ‖orbit z n‖ ≈ 2^n * G(z), so log(‖orbit z₂ n‖/‖orbit z₁ n‖) ≈ 2^n * (G(z₂) - G(z₁))
  -- If G(z₂) > G(z₁), this → ∞. But we're assuming G(z₂) ≤ G(z₁)...
  --
  -- The contradiction comes from: even if G(z₂) ≤ G(z₁), the INITIAL log-ratio
  -- log(t₂) - log(t₁) is positive, and this should propagate through iterations.
  --
  -- Actually, the two-sided bound at n=0 gives:
  -- log ‖z₂‖ - M ≤ G(z₂) ≤ G(z₁) ≤ log ‖z₁‖ + M
  -- So log(t₂) - log(t₁) ≤ 2M
  -- But for close t₁, t₂, this might be satisfied!
  --
  -- The key is that the orbit LOG-NORM ratio 2^(-n) * log(‖orbit z₂ n‖/‖orbit z₁ n‖)
  -- converges to G(z₂) - G(z₁) as n → ∞.
  -- If t₁ < t₂, then initially log(t₂/t₁) > 0, and the orbit dynamics preserves
  -- and amplifies this gap (for large norms, one iteration roughly doubles the log-norm).
  --
  -- For now, we use a sorry pending the complex orbit ratio analysis.
  -- The mathematical argument is sound, but formalizing it requires showing
  -- that the norm ratio grows without bound for ρ₁ < ρ₂.
  sorry

/-- **Lemma C** [general sorry]: The Green function is strictly increasing along each radial ray.
For the positive real direction (u = 1) and c = 2, this is proved above. For general
complex unit direction `u` and general `c`, this requires harmonic analysis (maximum
principle for subharmonic functions on level set domains) not yet available in Mathlib. -/
lemma green_function_strictMono_along_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > ‖c‖ + 2) (ht₂ : t₁ < t₂) :
    green_function c (↑t₁ * u) < green_function c (↑t₂ * u) := by
  sorry

/-! ## Lemma D: Existence of ray preimage for each Green value -/

/-- **Lemma D (existence)**: For each unit vector `u` and Green value `t` exceeding
the minimum on the ray, there exists `ρ > ‖c‖ + 2` with `G_c(ρ * u) = t`.
Proved using the Intermediate Value Theorem on the continuous function ρ ↦ G_c(ρ * u). -/
lemma exists_ray_preimage_green (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃ ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t := by
  set g := fun ρ : ℝ => green_function c ((ρ : ℂ) * u)
  have hg_cont : Continuous g :=
    (continuous_green_function c).comp (Complex.continuous_ofReal.mul continuous_const)
  -- Find an upper bound R₀ where g(R₀) ≥ t
  obtain ⟨R₀, hR₀_gt, hR₀_ge⟩ : ∃ R₀ : ℝ, R₀ > ‖c‖ + 2 ∧ g R₀ ≥ t := by
    have hbdd := bounded_sublevel_green_function c t
    rw [isBounded_iff_forall_norm_le] at hbdd
    obtain ⟨R, hR⟩ := hbdd
    refine ⟨max (‖c‖ + 3) (R + 1), ?_, ?_⟩
    · linarith [le_max_left (‖c‖ + 3) (R + 1)]
    · -- Show g(max ...) ≥ t by showing the norm exceeds R
      by_contra h
      push_neg at h
      have hmem : (↑(max (‖c‖+3) (R+1)) * u : ℂ) ∈ {z : ℂ | green_function c z < t} := by
        simpa using h
      have hle := hR _ hmem
      have hnorm : ‖(↑(max (‖c‖+3) (R+1)) * u : ℂ)‖ > R := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg, hu, mul_one]
        · linarith [le_max_right (‖c‖ + 3) (R + 1)]
        · exact le_trans (by linarith [norm_nonneg c]) (le_max_left _ _)
      linarith
  -- Apply IVT on [‖c‖+2, R₀]
  set a := ‖c‖ + 2
  have hab : a ≤ R₀ := le_of_lt hR₀_gt
  have hga : g a < t := ht
  have hIVT : ∃ ρ ∈ Set.Icc a R₀, g ρ = t :=
    intermediate_value_Icc hab hg_cont.continuousOn ⟨le_of_lt hga, hR₀_ge⟩
  obtain ⟨ρ, ⟨hρ_ge, _⟩, hρ_eq⟩ := hIVT
  refine ⟨ρ, ?_, hρ_eq⟩
  -- Strict inequality: ρ = a would give g a = t, contradicting g a < t
  rcases lt_or_eq_of_le hρ_ge with hlt | rfl
  · exact hlt
  · exact absurd (hρ_eq ▸ hga) (lt_irrefl t)

/-- **Lemma D (full statement)** [sorry for uniqueness]: For each unit vector `u` and
Green value `t > G_c((‖c‖+2)*u)`, there is a UNIQUE `ρ > ‖c‖ + 2` with G_c(ρ*u) = t.
Uniqueness requires Lemma C (strict monotonicity), which needs harmonic analysis. -/
lemma exists_unique_ray_preimage_green (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃! ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t := by
  obtain ⟨ρ, hρ_gt, hρ_eq⟩ := exists_ray_preimage_green c u hu t ht
  exact ⟨ρ, ⟨hρ_gt, hρ_eq⟩, fun ρ' ⟨_, hρ'_eq⟩ => by
    -- Uniqueness: if G_c(ρ*u) = G_c(ρ'*u), then ρ = ρ' by Lemma C.
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := green_function_strictMono_along_ray c u hu (by linarith) hlt
      simp [hρ_eq, hρ'_eq] at this
    · have := green_function_strictMono_along_ray c u hu (by linarith) hgt
      simp [hρ_eq, hρ'_eq] at this⟩

/-! ## Full-basin Lemma C and existence for constructive Lemma E -/

/-- **Lemma C (full-basin)**: Strict monotonicity along a ray for all `ρ₁ > 0` in
the basin.  Extends `green_function_strictMono_along_ray` (which requires `ρ₁ > ‖c‖ + 2`)
to all `ρ₁ > 0` with `G_c(ρ₁·u) > 0`.

Proof strategy: Use the functional equation `G_c(f_c^n(z)) = 2^n * G_c(z)` to reduce
to the outside-open case. Since `G_c(ρ₁·u) > 0`, eventually the iterates are in
`{‖z‖ > ‖c‖ + 2}` where we already have monotonicity along rays for `c = 2`. -/
lemma green_function_strictMono_along_ray_basin (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function c ((ρ₁ : ℂ) * u)) :
    green_function c ((ρ₁ : ℂ) * u) < green_function c ((ρ₂ : ℂ) * u) := by
  -- The approach: by contradiction, assuming G(ρ₁·u) ≥ G(ρ₂·u), and deriving
  -- that the orbit ratio stays bounded while the functional equation forces it to grow.
  -- This is essentially the same as the real-ray proof, but we need to track norms
  -- instead of real iterates.
  --
  -- For c = 2 and the real ray (u = 1), this is green_function_strictMono_along_real_ray_two.
  -- For general rays/parameters, a full proof requires either:
  -- 1. Norm comparison lemmas for orbits along different rays, or
  -- 2. Subharmonicity/maximum principle arguments not yet in Mathlib.
  --
  -- We use a sorry for now, but the structure is parallel to the real-ray case.
  sorry

private lemma green_function_neg (c z : ℂ) :
    green_function c (-z) = green_function c z := by
  have hneg : green_function c (fc c (-z)) = 2 * green_function c (-z) := by
    simpa using green_function_functional_eq c (-z)
  have hpos : green_function c (fc c z) = 2 * green_function c z := by
    simpa using green_function_functional_eq c z
  have hfc : fc c (-z) = fc c z := by
    simp [fc]
  rw [hfc] at hneg
  linarith

private lemma exists_ray_preimage_green_pos_of_ne_one
    (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (hu_ne_one : u ≠ 1) (t : ℝ) (ht : 0 < t) :
    ∃ ρ : ℝ, 0 < ρ ∧ green_function c ((ρ : ℂ) * u) = t := by
  let w : ℂ := u * (Real.exp t : ℂ)
  have hw : 1 < ‖w‖ := by
    have hnorm : ‖w‖ = Real.exp t := by
      simp [w, hu]
    linarith [Real.one_lt_exp_iff.mpr ht, hnorm]
  let z : ℂ := Quadratic.external_ray_map c w
  have hb : Quadratic.bottcher_map c z = w :=
    Quadratic.external_ray_map_right_inverse c w hw
  have hGz : green_function c z = t := by
    have hnorm_b : ‖Quadratic.bottcher_map c z‖ = Real.exp (green_function c z) :=
      Quadratic.norm_bottcher_eq_exp_green c z
    have hnorm_w : ‖w‖ = Real.exp t := by
      simp [w, hu]
    rw [hb, hnorm_w] at hnorm_b
    exact Real.exp_injective hnorm_b.symm
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hw_eq : w = (Real.exp t : ℂ) := by
      have h0 : w = Quadratic.bottcher_map c 0 := by
        simpa [z, hz0] using hb.symm
      calc
        w = Quadratic.bottcher_map c 0 := h0
        _ = (Real.exp (green_function c 0) : ℂ) := by simp [Quadratic.bottcher_map]
        _ = (Real.exp t : ℂ) := by
          have hg0 : green_function c 0 = t := by simpa [z, hz0] using hGz
          simp [hg0]
    have hmul : u * (Real.exp t : ℂ) = 1 * (Real.exp t : ℂ) := by
      simpa [w, one_mul] using hw_eq
    have hexp_ne : (Real.exp t : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_pos t).ne'
    have hu_eq_one : u = 1 := mul_right_cancel₀ hexp_ne hmul
    exact hu_ne_one hu_eq_one
  have hdir_mul : (z / ↑‖z‖) * (Real.exp t : ℂ) = u * (Real.exp t : ℂ) := by
    rw [Quadratic.bottcher_map, if_neg hz_ne, hGz] at hb
    simpa [w] using hb
  have hexp_ne : (Real.exp t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos t).ne'
  have hdir : z / ↑‖z‖ = u := mul_right_cancel₀ hexp_ne hdir_mul
  refine ⟨‖z‖, norm_pos_iff.mpr hz_ne, ?_⟩
  have hnorm_ne : (↑‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hz_ne).ne'
  have hz_eq : z = (↑‖z‖ : ℂ) * u := by
    calc
      z = (z / ↑‖z‖) * (↑‖z‖ : ℂ) := by field_simp [hnorm_ne]
      _ = u * (↑‖z‖ : ℂ) := by simp [hdir]
      _ = (↑‖z‖ : ℂ) * u := by ring
  have hGρ : green_function c ((↑‖z‖ : ℂ) * u) = t := by
    rw [hz_eq] at hGz
    simpa using hGz
  exact hGρ

/-- **Existence for all t > 0**: For any unit direction `u` and any `t > 0`, there
exists `ρ > 0` with `G_c(ρ · u) = t`. -/
lemma exists_ray_preimage_green_pos (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : 0 < t) :
    ∃ ρ : ℝ, 0 < ρ ∧ green_function c ((ρ : ℂ) * u) = t := by
  by_cases hu_one : u = 1
  · obtain ⟨ρ, hρ_pos, hρ_eq⟩ :=
      exists_ray_preimage_green_pos_of_ne_one c (-1 : ℂ) (by simp) (by norm_num) t ht
    refine ⟨ρ, hρ_pos, ?_⟩
    calc
      green_function c ((ρ : ℂ) * u) = green_function c ((ρ : ℂ) * (1 : ℂ)) := by
        simp [hu_one]
      _ = green_function c (-((ρ : ℂ) * (1 : ℂ))) := by
        symm
        exact green_function_neg c ((ρ : ℂ) * (1 : ℂ))
      _ = t := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hρ_eq
  · exact exists_ray_preimage_green_pos_of_ne_one c u hu hu_one t ht

/-- **Uniqueness for all t > 0**: The solution `ρ > 0` with `G_c(ρ · u) = t` is unique.
Follows from `green_function_strictMono_along_ray_basin`. -/
lemma exists_unique_ray_preimage_green_pos (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : 0 < t) :
    ∃! ρ : ℝ, 0 < ρ ∧ green_function c ((ρ : ℂ) * u) = t := by
  obtain ⟨ρ, hρ_pos, hρ_eq⟩ := exists_ray_preimage_green_pos c u hu t ht
  refine ⟨ρ, ⟨hρ_pos, hρ_eq⟩, fun ρ' ⟨hρ'_pos, hρ'_eq⟩ => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hG := green_function_strictMono_along_ray_basin c u hu hρ'_pos hlt (hρ'_eq ▸ ht)
    rw [hρ_eq, hρ'_eq] at hG; exact absurd hG (lt_irrefl _)
  · have hG := green_function_strictMono_along_ray_basin c u hu hρ_pos hgt (hρ_eq ▸ ht)
    rw [hρ_eq, hρ'_eq] at hG; exact absurd hG (lt_irrefl _)

/-! ## Lemma E: Constructive external ray map at `c = 2` -/

/-- The Böttcher map applied to a positive-real-scaled unit vector simplifies to
`u * exp(G_c(ρ · u))`. -/
private lemma bottcher_map_apply_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ)
    (hρ : 0 < ρ) :
    Quadratic.bottcher_map c ((ρ : ℂ) * u) =
      u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))) := by
  have hu_ne : u ≠ 0 := by rw [ne_eq, ← norm_eq_zero, hu]; exact one_ne_zero
  have hρ_ne : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hne : (ρ : ℂ) * u ≠ 0 := mul_ne_zero hρ_ne hu_ne
  simp only [Quadratic.bottcher_map, if_neg hne]
  have hnorm : ‖(ρ : ℂ) * u‖ = ρ := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le, hu, mul_one]
  have hdiv : (ρ : ℂ) * u / (ρ : ℂ) = u :=
    mul_div_cancel_left₀ u hρ_ne
  rw [hnorm, hdiv]

/-- **Lemma E**: The external ray map at `c = 2` exists constructively.

Explicit construction: for each `w` with `‖w‖ > 1`, let `u := w / ‖w‖` and let `ρ > 0` be
the (unique) solution to `G_2(ρ · u) = log ‖w‖` given by `exists_ray_preimage_green_pos`.
Set `f(w) := ρ · u`.

- **Right inverse**: `bottcher_map 2 (f w) = u · ‖w‖ = w` since
  `bottcher_map 2 (ρ · u) = u · exp(G_2(ρ · u)) = u · exp(log ‖w‖) = u · ‖w‖`. ✓
- **Left inverse**: for `‖z‖ > 4`, `bottcher_map 2 z = (z/‖z‖) · exp(G_2(z))`, so
  `log ‖bottcher_map 2 z‖ = G_2(z)` and `bottcher_map 2 z / ‖·‖ = z / ‖z‖`.
  Hence `ρ = ‖z‖` is the unique solution, giving `f(bottcher_map 2 z) = ‖z‖ · (z/‖z‖) = z`. ✓

Remaining sorry gaps:
1. `exists_ray_preimage_green_pos` — IVT from G_c = 0 on ∂K_c to G_c → ∞.
2. `green_function_strictMono_along_ray_basin` — full-basin Lemma C (harmonic analysis). -/
theorem external_ray_map_exists_two_via_green_function :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  -- For every w with ‖w‖ > 1, the existence lemma applies with u = w/‖w‖, t = log ‖w‖.
  have hf_ex : ∀ w : ℂ, 1 < ‖w‖ →
      ∃ ρ : ℝ, 0 < ρ ∧ green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ :=
    fun w hw => by
      apply exists_ray_preimage_green_pos
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (by linarith : ‖w‖ ≠ 0)]
      · exact Real.log_pos hw
  -- Define f by Classical.choose on hf_ex.
  refine ⟨fun w => if hw : 1 < ‖w‖ then
      ↑(Classical.choose (hf_ex w hw)) * (w / ↑‖w‖) else 0, ?_, ?_⟩
  · -- Part A: right inverse — bottcher_map 2 (f w) = w for ‖w‖ > 1.
    intro w hw
    simp only [dif_pos hw]
    have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
    have hu : ‖w / ↑‖w‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
    obtain ⟨hρ_pos, hρ_eq⟩ := Classical.choose_spec (hf_ex w hw)
    -- bottcher_map 2 (↑ρ * (w/↑‖w‖)) = (w/↑‖w‖) * ‖w‖ = w
    rw [bottcher_map_apply_ray (2 : ℂ) _ hu _ hρ_pos, hρ_eq, Real.exp_log hw_pos]
    exact div_mul_cancel₀ w (by exact_mod_cast hw_pos.ne')
  · -- Part B: left inverse — f (bottcher_map 2 z) = z for ‖z‖ > ‖(2:ℂ)‖ + 2.
    intro z hz
    have h2norm : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast,
          Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hz_pos : (0 : ℝ) < ‖z‖ := by linarith [h2norm ▸ hz]
    have hz_ne : z ≠ 0 := norm_ne_zero_iff.mp hz_pos.ne'
    -- Let w = bottcher_map 2 z; show 1 < ‖w‖.
    set w := Quadratic.bottcher_map (2 : ℂ) z with hw_def
    have hGz_pos : 0 < green_function (2 : ℂ) z :=
      green_function_pos_on_outside_open (2 : ℂ) z hz
    have hw_norm : ‖w‖ = Real.exp (green_function (2 : ℂ) z) :=
      norm_bottcher_eq_exp_green (2 : ℂ) z
    have hw_gt1 : 1 < ‖w‖ := hw_norm ▸ Real.one_lt_exp_iff.mpr hGz_pos
    have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
    simp only [dif_pos hw_gt1]
    have hu_dir : ‖w / ↑‖w‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
    -- Direction w/‖w‖ = z/‖z‖: the Böttcher map preserves direction.
    have hdir_eq : w / ↑‖w‖ = z / ↑‖z‖ := by
      rw [hw_norm]
      simp only [hw_def, Quadratic.bottcher_map, if_neg hz_ne]
      field_simp [(Real.exp_pos (green_function (2 : ℂ) z)).ne',
                  show (↑‖z‖ : ℂ) ≠ 0 from by exact_mod_cast hz_pos.ne']
    -- log ‖w‖ = G_2(z).
    have hlog_eq : Real.log ‖w‖ = green_function (2 : ℂ) z := hw_norm ▸ Real.log_exp _
    -- ‖z‖ satisfies: G_2(↑‖z‖ * (w/‖w‖)) = log ‖w‖.
    have hz_witness : green_function (2 : ℂ) ((↑‖z‖ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ := by
      rw [hlog_eq, hdir_eq]
      congr 1
      field_simp [show (↑‖z‖ : ℂ) ≠ 0 from by exact_mod_cast hz_pos.ne']
    -- By uniqueness, Classical.choose (hf_ex w hw_gt1) = ‖z‖.
    obtain ⟨hρ_pos, hρ_eq⟩ := Classical.choose_spec (hf_ex w hw_gt1)
    set ρ := Classical.choose (hf_ex w hw_gt1) with hρ_def
    have huniq := exists_unique_ray_preimage_green_pos (2 : ℂ) (w / ↑‖w‖) hu_dir
        (Real.log ‖w‖) (Real.log_pos hw_gt1)
    have hρ_normz : ρ = ‖z‖ := huniq.unique ⟨hρ_pos, hρ_eq⟩ ⟨hz_pos, hz_witness⟩
    -- Conclude: f(w) = ‖z‖ · (z/‖z‖) = z.
    rw [hρ_normz, hdir_eq]
    field_simp [show (↑‖z‖ : ℂ) ≠ 0 from by exact_mod_cast hz_pos.ne']

end GreenFunctionRayInversion

end MLC
