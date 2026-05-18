import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.ParaPuzzleBasis
import Mlc.Quadratic.Complex.Axioms
import Mathlib.Topology.Order.IntermediateValue

/-!
# Green Function Ray Inversion at `c = 2`

This file formalizes inversion constructors for the current explicit
`bottcher_map` proxy at `c = 2` via the Green function.

## Definition

`bottcher_map 2 z = polar_green_map 2 z = (z / ‖z‖) * exp(green_function 2 z)`
away from zero, with the current total proxy branch at `z = 0`.

The inverse `f` maps each `w` (with `‖w‖ > 1`) to the unique point `z` in the
basin of infinity satisfying:
- `arg(z) = arg(w)` (same direction)
- `green_function 2 z = Real.log ‖w‖` (matching Green function value)

## Plan status (Lemmas A–E)
- [x] Lemma A: `green_function_pos_on_outside_open` — follows from `green_function_pos_of_basin`.
- [x] Lemma B: `green_function_tendsto_atTop` — follows from `bounded_sublevel_green_function`.
- [x*] Lemma C: seam-parameterized strict-monotonicity wrappers are in place;
       fully constructive full-basin monotonicity remains open.
- [x] Lemma D: `exists_ray_preimage_green` and uniqueness wrappers are in place
       (uniqueness routed through strict-mono assumptions/seams).
- [x] Lemma E: seam-minimal constructive `c = 2` inversion constructors are in place.
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

/-- At `c = 2`, the Green function is globally even. -/
lemma green_function_neg_eq_two (z : ℂ) :
    green_function (2 : ℂ) (-z) = green_function (2 : ℂ) z := by
  have hneg := green_function_functional_eq (2 : ℂ) (-z)
  have hpos := green_function_functional_eq (2 : ℂ) z
  have hfc : fc (2 : ℂ) (-z) = fc (2 : ℂ) z := by
    simp [fc]
  have htwice : 2 * green_function (2 : ℂ) (-z) = 2 * green_function (2 : ℂ) z := by
    calc
      2 * green_function (2 : ℂ) (-z)
          = green_function (2 : ℂ) (fc (2 : ℂ) (-z)) := by
              simpa using hneg.symm
      _ = green_function (2 : ℂ) (fc (2 : ℂ) z) := by
            simpa [hfc]
      _ = 2 * green_function (2 : ℂ) z := by
            simpa using hpos
  linarith

/-- At `c = 2`, the explicit `polar_green_map` proxy is odd away from `0`. -/
lemma polar_green_map_neg_eq_neg_two_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    Quadratic.polar_green_map (2 : ℂ) (-z) = - Quadratic.polar_green_map (2 : ℂ) z := by
  have hneg : (-z : ℂ) ≠ 0 := by simpa using neg_ne_zero.mpr hz
  have hnorm_ne : (↑‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.2 hz)
  have hdir : (-z : ℂ) / ↑‖-z‖ = -(z / ↑‖z‖) := by
    rw [norm_neg]
    field_simp [hnorm_ne]
  unfold Quadratic.polar_green_map
  simp [hneg, hz, green_function_neg_eq_two z, hdir]
  ring

private lemma zero_mem_basin_two_local : (0 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := by
  have h6_basin : (6 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := by
    apply outside_open_subset_basin (2 : ℂ)
    norm_num
  have h2_basin : (2 : ℂ) ∈ Quadratic.basin_of_infinity (2 : ℂ) := by
    have h2image : quadratic_map (2 : ℂ) (2 : ℂ) = 6 := by
      norm_num [quadratic_map]
    apply (basin_of_infinity_preimage_subset (2 : ℂ))
    simpa [Set.preimage, h2image] using h6_basin
  have h0image : quadratic_map (2 : ℂ) (0 : ℂ) = 2 := by
    norm_num [quadratic_map]
  apply (basin_of_infinity_preimage_subset (2 : ℂ))
  simpa [Set.preimage, h0image] using h2_basin

/-- The current explicit `polar_green_map` proxy at `c = 2` does not vanish at `0`. -/
lemma polar_green_map_zero_ne_zero_two :
    Quadratic.polar_green_map (2 : ℂ) 0 ≠ 0 := by
  have hgreen_pos : 0 < Quadratic.green_function (2 : ℂ) 0 :=
    green_function_pos_of_basin (2 : ℂ) 0 zero_mem_basin_two_local
  simpa [Quadratic.polar_green_map] using
    (show (1 : ℂ) * ↑(Real.exp (Quadratic.green_function (2 : ℂ) 0)) ≠ 0 from
      mul_ne_zero one_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'))

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

/-- For `c = 2` and positive real radii, strict monotonicity along `u = 1`.
This lifts the `ρ₁ > 4` result by iterating twice into the outside-open range
and pulling back via `G(f²(z)) = 4 * G(z)`. -/
lemma green_function_strictMono_along_real_ray_two_pos {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂)
    (hρ₁ : 0 < ρ₁) :
    green_function (2 : ℂ) (↑ρ₁ : ℂ) < green_function (2 : ℂ) (↑ρ₂ : ℂ) := by
  have hiter2 : f2 ^[2] ρ₁ < f2 ^[2] ρ₂ :=
    f2_iterate_strictMono h hρ₁ 2
  have hiter2_gt4 : f2 ^[2] ρ₁ > 4 := by
    simp only [Function.iterate_succ_apply', f2]
    nlinarith [sq_nonneg ρ₁]
  have hmono_iter :
      green_function (2 : ℂ) ((f2 ^[2] ρ₁ : ℂ)) <
        green_function (2 : ℂ) ((f2 ^[2] ρ₂ : ℂ)) :=
    green_function_strictMono_along_real_ray_two hiter2 hiter2_gt4
  have horb₁ : orbit (2 : ℂ) ((ρ₁ : ℂ)) 2 = ((f2 ^[2] ρ₁ : ℂ)) := by
    simpa using orbit_two_ofReal ρ₁ 2
  have horb₂ : orbit (2 : ℂ) ((ρ₂ : ℂ)) 2 = ((f2 ^[2] ρ₂ : ℂ)) := by
    simpa using orbit_two_ofReal ρ₂ 2
  have hpull₁ :
      green_function (2 : ℂ) ((f2 ^[2] ρ₁ : ℂ)) =
        4 * green_function (2 : ℂ) ((ρ₁ : ℂ)) := by
    calc
      green_function (2 : ℂ) ((f2 ^[2] ρ₁ : ℂ))
          = green_function (2 : ℂ) (orbit (2 : ℂ) ((ρ₁ : ℂ)) 2) := by
              exact congrArg (green_function (2 : ℂ)) horb₁.symm
      _ = 2 ^ 2 * green_function (2 : ℂ) ((ρ₁ : ℂ)) :=
            green_function_orbit_eq (2 : ℂ) ((ρ₁ : ℂ)) 2
      _ = 4 * green_function (2 : ℂ) ((ρ₁ : ℂ)) := by norm_num
  have hpull₂ :
      green_function (2 : ℂ) ((f2 ^[2] ρ₂ : ℂ)) =
        4 * green_function (2 : ℂ) ((ρ₂ : ℂ)) := by
    calc
      green_function (2 : ℂ) ((f2 ^[2] ρ₂ : ℂ))
          = green_function (2 : ℂ) (orbit (2 : ℂ) ((ρ₂ : ℂ)) 2) := by
              exact congrArg (green_function (2 : ℂ)) horb₂.symm
      _ = 2 ^ 2 * green_function (2 : ℂ) ((ρ₂ : ℂ)) :=
            green_function_orbit_eq (2 : ℂ) ((ρ₂ : ℂ)) 2
      _ = 4 * green_function (2 : ℂ) ((ρ₂ : ℂ)) := by norm_num
  rw [hpull₁, hpull₂] at hmono_iter
  linarith

/-- For `c = 2`, the Green function is even on the real axis:
`G₂(-ρ) = G₂(ρ)`. -/
lemma green_function_neg_real_eq_two (ρ : ℝ) :
    green_function (2 : ℂ) ((-ρ : ℝ) : ℂ) = green_function (2 : ℂ) ((ρ : ℝ) : ℂ) := by
  have hneg := green_function_functional_eq (2 : ℂ) (((-ρ : ℝ) : ℂ))
  have hpos := green_function_functional_eq (2 : ℂ) ((ρ : ℝ) : ℂ)
  have hfc :
      fc (2 : ℂ) (((-ρ : ℝ) : ℂ)) = fc (2 : ℂ) ((ρ : ℝ) : ℂ) := by
    simp [fc]
  have hneg' :
      green_function (2 : ℂ) (fc (2 : ℂ) ((ρ : ℝ) : ℂ)) =
        2 * green_function (2 : ℂ) (((-ρ : ℝ) : ℂ)) := by
    calc
      green_function (2 : ℂ) (fc (2 : ℂ) ((ρ : ℝ) : ℂ))
          = green_function (2 : ℂ) (fc (2 : ℂ) (((-ρ : ℝ) : ℂ))) := by
              simpa [hfc] using congrArg (green_function (2 : ℂ)) hfc.symm
      _ = 2 * green_function (2 : ℂ) (((-ρ : ℝ) : ℂ)) := by
              simpa using hneg
  have hpos' :
      green_function (2 : ℂ) (fc (2 : ℂ) ((ρ : ℝ) : ℂ)) =
        2 * green_function (2 : ℂ) ((ρ : ℝ) : ℂ) := by
    simpa using hpos
  linarith

/-- **Lemma C (real case, opposite direction)**:
For `c = 2` and the negative real direction `u = -1`, the Green function is
strictly increasing with radius. -/
lemma green_function_strictMono_along_neg_real_ray_two {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂)
    (hρ₁ : ρ₁ > 4) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ)) <
      green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) := by
  have hreal : green_function (2 : ℂ) ((ρ₁ : ℝ) : ℂ) <
      green_function (2 : ℂ) ((ρ₂ : ℝ) : ℂ) :=
    green_function_strictMono_along_real_ray_two h hρ₁
  have hρ₁neg :
      green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ)) =
        green_function (2 : ℂ) ((ρ₁ : ℝ) : ℂ) := by
    simpa [mul_comm] using green_function_neg_real_eq_two ρ₁
  have hρ₂neg :
      green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) =
        green_function (2 : ℂ) ((ρ₂ : ℝ) : ℂ) := by
    simpa [mul_comm] using green_function_neg_real_eq_two ρ₂
  calc
    green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ))
        = green_function (2 : ℂ) ((ρ₁ : ℝ) : ℂ) := hρ₁neg
    _ < green_function (2 : ℂ) ((ρ₂ : ℝ) : ℂ) := hreal
    _ = green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) := hρ₂neg.symm

/-- For `c = 2` and positive real radii, strict monotonicity along `u = -1`. -/
lemma green_function_strictMono_along_neg_real_ray_two_pos {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂)
    (hρ₁ : 0 < ρ₁) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ)) <
      green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) := by
  have hreal : green_function (2 : ℂ) ((ρ₁ : ℝ) : ℂ) <
      green_function (2 : ℂ) ((ρ₂ : ℝ) : ℂ) :=
    green_function_strictMono_along_real_ray_two_pos h hρ₁
  have hρ₁neg :
      green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ)) =
        green_function (2 : ℂ) ((ρ₁ : ℝ) : ℂ) := by
    simpa [mul_comm] using green_function_neg_real_eq_two ρ₁
  have hρ₂neg :
      green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) =
        green_function (2 : ℂ) ((ρ₂ : ℝ) : ℂ) := by
    simpa [mul_comm] using green_function_neg_real_eq_two ρ₂
  calc
    green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ))
        = green_function (2 : ℂ) ((ρ₁ : ℝ) : ℂ) := hρ₁neg
    _ < green_function (2 : ℂ) ((ρ₂ : ℝ) : ℂ) := hreal
    _ = green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) := hρ₂neg.symm

/-- Full-basin seam-shaped corollary for the positive real direction `u = 1`.
The positivity premise is currently unused because monotonicity now holds for
all positive radii on this direction. -/
lemma green_function_strictMono_along_real_ray_basin_two
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (_hG : 0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * (1 : ℂ))) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * (1 : ℂ)) <
      green_function (2 : ℂ) ((ρ₂ : ℂ) * (1 : ℂ)) := by
  simpa using green_function_strictMono_along_real_ray_two_pos h12 hρ₁

/-- Full-basin seam-shaped corollary for the negative real direction `u = -1`.
As above, the positivity premise is unused for this direction. -/
lemma green_function_strictMono_along_neg_real_ray_basin_two
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (_hG : 0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ))) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * (-1 : ℂ)) <
      green_function (2 : ℂ) ((ρ₂ : ℂ) * (-1 : ℂ)) := by
  exact green_function_strictMono_along_neg_real_ray_two_pos h12 hρ₁

/-- Partial seam at `c = 2`: full-basin strict radial monotonicity restricted
to real directions `u = 1` or `u = -1`. -/
def GreenFunctionStrictMonoAlongRealDirectionsTwoSeam : Prop :=
  ∀ (u : ℂ) (_hu : ‖u‖ = 1), (u = (1 : ℂ) ∨ u = (-1 : ℂ)) →
    ∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₁ < ρ₂ →
      0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u) →
        green_function (2 : ℂ) ((ρ₁ : ℂ) * u) <
          green_function (2 : ℂ) ((ρ₂ : ℂ) * u)

/-- Constructive witness of strict radial monotonicity on real directions. -/
lemma green_function_strictMono_along_realDirections_two_constructive :
    GreenFunctionStrictMonoAlongRealDirectionsTwoSeam := by
  intro u hu hdir ρ₁ ρ₂ hρ₁ h12 hG
  rcases hdir with rfl | rfl
  · simpa using green_function_strictMono_along_real_ray_basin_two hρ₁ h12 hG
  · simpa using green_function_strictMono_along_neg_real_ray_basin_two hρ₁ h12 hG

/-- Residual seam at `c = 2`: strict radial monotonicity on nonreal
unit directions (all directions except `±1`). -/
def GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam : Prop :=
  ∀ (u : ℂ) (_hu : ‖u‖ = 1), ¬ (u = (1 : ℂ) ∨ u = (-1 : ℂ)) →
    ∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₁ < ρ₂ →
      0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u) →
        green_function (2 : ℂ) ((ρ₁ : ℂ) * u) <
          green_function (2 : ℂ) ((ρ₂ : ℂ) * u)

/-- Replacement-target seam at `c = 2` for full-basin strict radial monotonicity. -/
def GreenFunctionStrictMonoAlongRayBasinTwoSeam : Prop :=
  ∀ (u : ℂ) (_hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₁ < ρ₂ →
      0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u) →
        green_function (2 : ℂ) ((ρ₁ : ℂ) * u) <
          green_function (2 : ℂ) ((ρ₂ : ℂ) * u)

/-- Full seam assembled from the constructive real-direction seam and a residual
nonreal-direction seam target. -/
lemma green_function_strictMono_along_ray_basin_two_of_realDirections_of_nonRealDirections
    (hreal : GreenFunctionStrictMonoAlongRealDirectionsTwoSeam)
    (hnonreal : GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam) :
    GreenFunctionStrictMonoAlongRayBasinTwoSeam := by
  intro u hu ρ₁ ρ₂ hρ₁ h12 hG
  by_cases hdir : u = (1 : ℂ) ∨ u = (-1 : ℂ)
  · exact hreal u hu hdir hρ₁ h12 hG
  · exact hnonreal u hu hdir hρ₁ h12 hG

/-- Full `c = 2` strict radial monotonicity from the single residual
nonreal-direction seam plus the already-constructive real-direction seam. -/
lemma green_function_strictMono_along_ray_basin_two_of_nonRealDirections
    (hnonreal : GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam) :
    GreenFunctionStrictMonoAlongRayBasinTwoSeam :=
  green_function_strictMono_along_ray_basin_two_of_realDirections_of_nonRealDirections
    green_function_strictMono_along_realDirections_two_constructive
    hnonreal

/-- Restrict full `c = 2` ray-basin strict monotonicity to the residual
nonreal-direction seam target. -/
lemma green_function_strictMono_along_nonRealDirections_two_of_ray_basin_two
    (hmono : GreenFunctionStrictMonoAlongRayBasinTwoSeam) :
    GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam := by
  intro u hu hnonreal ρ₁ ρ₂ hρ₁ h12 hG
  exact hmono u hu hρ₁ h12 hG

/-- Residual nonreal-direction seam is equivalent to full seam once the
constructive real-direction branch is fixed. -/
lemma green_function_strictMono_along_nonRealDirections_two_iff_ray_basin_two :
    GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam ↔
      GreenFunctionStrictMonoAlongRayBasinTwoSeam := by
  constructor
  · exact green_function_strictMono_along_ray_basin_two_of_nonRealDirections
  · exact green_function_strictMono_along_nonRealDirections_two_of_ray_basin_two

/-- Axiom-seeded residual strict-mono seam restricted to nonreal directions.
This isolates the remaining axiom pressure after the constructive real-direction
monotonicity upgrade. -/
lemma green_function_strictMono_along_nonRealDirections_two_axiom_seed :
    GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam := by
  intro u hu hnonreal ρ₁ ρ₂ hρ₁ h12 hG
  exact Quadratic.green_function_strictMono_along_ray_basin_seam
    (2 : ℂ) u hu hρ₁ h12 hG

/-- Mixed seed for the full seam: constructive on real directions, axiom-seeded
only on residual nonreal directions. -/
lemma green_function_strictMono_along_ray_basin_two_mixed_seed :
    GreenFunctionStrictMonoAlongRayBasinTwoSeam :=
  green_function_strictMono_along_ray_basin_two_of_nonRealDirections
    green_function_strictMono_along_nonRealDirections_two_axiom_seed

/-- Axiom-seeded provider for the `c = 2` full-basin strict radial monotonicity
replacement seam. -/
lemma green_function_strictMono_along_ray_basin_two_axiom_seed :
    GreenFunctionStrictMonoAlongRayBasinTwoSeam :=
  green_function_strictMono_along_ray_basin_two_mixed_seed

/-- Specialized `c = 2` full-basin strict radial monotonicity from the
replacement seam. -/
lemma green_function_strictMono_along_ray_basin_two_of_seam
    (hmono : GreenFunctionStrictMonoAlongRayBasinTwoSeam)
    (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u)) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * u) <
      green_function (2 : ℂ) ((ρ₂ : ℂ) * u) :=
  hmono u hu hρ₁ h12 hG

lemma green_function_strictMono_along_ray_basin_two
    (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function (2 : ℂ) ((ρ₁ : ℂ) * u)) :
    green_function (2 : ℂ) ((ρ₁ : ℂ) * u) <
      green_function (2 : ℂ) ((ρ₂ : ℂ) * u) :=
  green_function_strictMono_along_ray_basin_two_of_seam
    green_function_strictMono_along_ray_basin_two_axiom_seed
    u hu hρ₁ h12 hG

/-- **Lemma C (full-basin)**: Strict monotonicity along a ray for all `ρ₁ > 0` in
the basin.  Extends outside-open strict monotonicity to all `ρ₁ > 0` with
`G_c(ρ₁·u) > 0`.

Proof strategy: Use the functional equation `G_c(f_c^n(z)) = 2^n * G_c(z)` to reduce
to the outside-open case. Since `G_c(ρ₁·u) > 0`, eventually the iterates are in
`{‖z‖ > ‖c‖ + 2}`. -/
lemma green_function_strictMono_along_ray_basin (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function c ((ρ₁ : ℂ) * u)) :
    green_function c ((ρ₁ : ℂ) * u) < green_function c ((ρ₂ : ℂ) * u) := by
  exact Quadratic.green_function_strictMono_along_ray_basin_seam c u hu hρ₁ h12 hG

/-- **Lemma C**: The Green function is strictly increasing along each radial ray
outside-open. -/
lemma green_function_strictMono_along_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > ‖c‖ + 2) (ht₂ : t₁ < t₂) :
    green_function c (↑t₁ * u) < green_function c (↑t₂ * u) := by
  have ht₁_pos : 0 < t₁ := by
    linarith [norm_nonneg c]
  have hnorm₁ : ‖((t₁ : ℂ) * u)‖ = t₁ := by
    rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg ht₁_pos.le]
  have hG₁ : 0 < green_function c ((t₁ : ℂ) * u) := by
    apply green_function_pos_on_outside_open c ((t₁ : ℂ) * u)
    linarith [ht₁, hnorm₁]
  exact green_function_strictMono_along_ray_basin c u hu ht₁_pos ht₂ hG₁

/-- **Lemma C (complex rays, c = 2)**: strict monotonicity along any unit ray,
specialized from the general outside-open ray seam. -/
lemma green_function_strictMono_along_ray_two_of_seam
    (hmono : GreenFunctionStrictMonoAlongRayBasinTwoSeam)
    (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₁ < t₂) :
    green_function (2 : ℂ) (↑t₁ * u) < green_function (2 : ℂ) (↑t₂ * u) := by
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast, norm_real,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have ht₁' : t₁ > ‖(2 : ℂ)‖ + 2 := by
    linarith [ht₁, h2norm]
  have ht₁_pos : 0 < t₁ := by linarith [ht₁]
  have hnorm₁ : ‖((t₁ : ℂ) * u)‖ = t₁ := by
    rw [norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg ht₁_pos.le]
  have hG₁ : 0 < green_function (2 : ℂ) ((t₁ : ℂ) * u) := by
    apply green_function_pos_on_outside_open (2 : ℂ) ((t₁ : ℂ) * u)
    linarith [ht₁', hnorm₁]
  exact green_function_strictMono_along_ray_basin_two_of_seam hmono u hu ht₁_pos ht₂ hG₁

/-- **Lemma C (complex rays, c = 2)**: strict monotonicity along any unit ray,
specialized from the `c = 2` seam target. -/
lemma green_function_strictMono_along_ray_two (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > 4) (ht₂ : t₁ < t₂) :
    green_function (2 : ℂ) (↑t₁ * u) < green_function (2 : ℂ) (↑t₂ * u) :=
  green_function_strictMono_along_ray_two_of_seam
    green_function_strictMono_along_ray_basin_two_axiom_seed
    u hu ht₁ ht₂

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

/-- **Lemma D (full statement, strict-mono parameterized)**: For each unit vector `u`
and Green value `t > G_c((‖c‖+2)*u)`, there is a unique `ρ > ‖c‖ + 2` with
`G_c(ρ*u) = t`, assuming strict monotonicity along the ray. -/
lemma exists_unique_ray_preimage_green_of_strictMono
    (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u))
    (hmono :
      ∀ {ρ₁ ρ₂ : ℝ}, ρ₁ > ‖c‖ + 2 → ρ₁ < ρ₂ →
        green_function c ((ρ₁ : ℂ) * u) < green_function c ((ρ₂ : ℂ) * u)) :
    ∃! ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t := by
  obtain ⟨ρ, hρ_gt, hρ_eq⟩ := exists_ray_preimage_green c u hu t ht
  refine ⟨ρ, ⟨hρ_gt, hρ_eq⟩, ?_⟩
  intro ρ' hρ'
  rcases hρ' with ⟨hρ'_gt, hρ'_eq⟩
  -- Uniqueness from strict monotonicity along the same ray.
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmono_lt := hmono hρ'_gt hlt
    simp [hρ_eq, hρ'_eq] at hmono_lt
  · have hmono_gt := hmono hρ_gt hgt
    simp [hρ_eq, hρ'_eq] at hmono_gt

/-- **Lemma D (full statement)**: For each unit vector `u` and Green value
`t > G_c((‖c‖+2)*u)`, there is a unique `ρ > ‖c‖ + 2` with `G_c(ρ*u) = t`. -/
lemma exists_unique_ray_preimage_green (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃! ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t := by
  exact exists_unique_ray_preimage_green_of_strictMono c u hu t ht
    (fun {_ρ₁ _ρ₂} hρ₁ h12 =>
      green_function_strictMono_along_ray c u hu hρ₁ h12)

/-- Corrected radial preimage existence: for target values above the ray's
outside-open anchor value, there is a radial preimage in outside-open. -/
lemma exists_ray_preimage_green_pos (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃ ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t := by
  exact exists_ray_preimage_green c u hu t ht

/-- Corrected radial preimage uniqueness above the outside-open anchor value. -/
lemma exists_unique_ray_preimage_green_pos (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃! ρ : ℝ, ρ > ‖c‖ + 2 ∧ green_function c ((ρ : ℂ) * u) = t :=
  exists_unique_ray_preimage_green c u hu t ht

/-- `c = 2` anchored uniqueness, specialized for normalized exterior direction
`w / ‖w‖` at target `log ‖w‖`. -/
lemma exists_unique_ray_preimage_green_two_anchor_of_seam
    (hmono : GreenFunctionStrictMonoAlongRayBasinTwoSeam)
    (w : ℂ) (hw : 1 < ‖w‖)
    (hlog_gt_anchor :
      green_function (2 : ℂ) (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) :
    ∃! ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
      green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ := by
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast,
      norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  set u : ℂ := w / ↑‖w‖
  have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
  have hu_dir : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
  have h_anchor_u :
      green_function (2 : ℂ) (((‖(2 : ℂ)‖ + 2 : ℝ) * u) : ℂ) < Real.log ‖w‖ := by
    simpa [u] using hlog_gt_anchor
  refine exists_unique_ray_preimage_green_of_strictMono (2 : ℂ) u hu_dir (Real.log ‖w‖)
    h_anchor_u ?_
  intro ρ₁ ρ₂ hρ₁ h12
  have hρ₁_gt4 : ρ₁ > 4 := by linarith [hρ₁, h2norm]
  exact green_function_strictMono_along_ray_two_of_seam hmono u hu_dir hρ₁_gt4 h12

/-- `c = 2` anchored uniqueness, specialized for normalized exterior direction
`w / ‖w‖` at target `log ‖w‖`. -/
lemma exists_unique_ray_preimage_green_two_anchor
    (w : ℂ) (hw : 1 < ‖w‖)
    (hlog_gt_anchor :
      green_function (2 : ℂ) (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) :
    ∃! ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
      green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ :=
  exists_unique_ray_preimage_green_two_anchor_of_seam
    green_function_strictMono_along_ray_basin_two_axiom_seed
    w hw hlog_gt_anchor

/-! ## Lemma E: Constructive external ray map at `c = 2` -/

/-- The Böttcher map applied to a positive-real-scaled unit vector simplifies to
`u * exp(G_c(ρ · u))`. -/
private lemma bottcher_map_apply_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (ρ : ℝ)
    (hρ : 0 < ρ) :
    Quadratic.bottcher_map c ((ρ : ℂ) * u) =
      u * ↑(Real.exp (green_function c ((ρ : ℂ) * u))) := by
  simpa using Quadratic.bottcher_map_apply_ray c u hu ρ hρ

/-- **Lemma E (seam-minimal uniqueness form)**: the external ray map at `c = 2`
from anchored uniqueness + anchor-gap seams.

Explicit construction: for each `w` with `‖w‖ > 1`, let `u := w / ‖w‖` and let `ρ > 0` be
the (unique) solution to `G_2(ρ · u) = log ‖w‖` given by `exists_ray_preimage_green_pos`.
Set `f(w) := ρ · u`.

- **Right inverse**: `bottcher_map 2 (f w) = u · ‖w‖ = w` since
  `bottcher_map 2 (ρ · u) = u · exp(G_2(ρ · u)) = u · exp(log ‖w‖) = u · ‖w‖`. ✓
- **Left inverse**: for `‖z‖ > 4`, `bottcher_map 2 z = (z/‖z‖) · exp(G_2(z))`, so
  `log ‖bottcher_map 2 z‖ = G_2(z)` and `bottcher_map 2 z / ‖·‖ = z / ‖z‖`.
  Hence `ρ = ‖z‖` is the unique solution, giving `f(bottcher_map 2 z) = ‖z‖ · (z/‖z‖) = z`. ✓

Current gap note:
1. Full constructive strict-monotonicity replacement for
   `green_function_strictMono_along_ray_basin_two_axiom_seed` remains open. -/
theorem external_ray_map_exists_two_via_green_function_of_uniquePreimageSeam
    (huniq_anchor :
      ∀ w : ℂ, 1 < ‖w‖ →
        green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖ →
          ∃! ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
            green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖)
    (hlog_gt_anchor :
      ∀ w : ℂ, 1 < ‖w‖ →
        green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  -- For every w with ‖w‖ > 1, apply corrected existence above the outside-open anchor.
  have hf_ex : ∀ w : ℂ, 1 < ‖w‖ →
      ∃ ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧ green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ :=
    fun w hw => by
      apply exists_ray_preimage_green_pos
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (by linarith : ‖w‖ ≠ 0)]
      · exact hlog_gt_anchor w hw
  -- Define f by Classical.choose on hf_ex.
  refine ⟨fun w => if hw : 1 < ‖w‖ then
      ↑(Classical.choose (hf_ex w hw)) * (w / ↑‖w‖) else 0, ?_, ?_⟩
  · -- Part A: right inverse — bottcher_map 2 (f w) = w for ‖w‖ > 1.
    intro w hw
    simp only [dif_pos hw]
    have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
    have hu : ‖w / ↑‖w‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
    obtain ⟨hρ_gt, hρ_eq⟩ := Classical.choose_spec (hf_ex w hw)
    have hρ_pos : 0 < Classical.choose (hf_ex w hw) := by
      linarith [hρ_gt, norm_nonneg (2 : ℂ)]
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
      have hu_z : ‖z / ↑‖z‖‖ = 1 := by
        rw [norm_div, Complex.norm_real, norm_norm, div_self hz_pos.ne']
      have hscale : ((‖z‖ : ℂ) * (z / ↑‖z‖)) = z := by
        field_simp [show (↑‖z‖ : ℂ) ≠ 0 from by exact_mod_cast hz_pos.ne',
          mul_comm, mul_left_comm, mul_assoc]
      have happlyz :
          Quadratic.bottcher_map (2 : ℂ) z =
            (z / ↑‖z‖) * ↑(Real.exp (green_function (2 : ℂ) z)) := by
        simpa [hscale] using
          (Quadratic.bottcher_map_apply_ray (2 : ℂ) (z / ↑‖z‖) hu_z ‖z‖ hz_pos)
      rw [hw_norm, hw_def, happlyz]
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
    obtain ⟨hρ_gt, hρ_eq⟩ := Classical.choose_spec (hf_ex w hw_gt1)
    set ρ := Classical.choose (hf_ex w hw_gt1) with hρ_def
    have _hlog_anchor :
        Real.log ‖w‖ >
          green_function (2 : ℂ) (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) := by
      exact hlog_gt_anchor w hw_gt1
    have huniq :
        ∃! ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧
          green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ :=
      huniq_anchor w hw_gt1 (hlog_gt_anchor w hw_gt1)
    have hz_gt_outside : ‖z‖ > ‖(2 : ℂ)‖ + 2 := by
      have h2norm : ‖(2 : ℂ)‖ = 2 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_cast,
            Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [hz]
    have hρ_normz : ρ = ‖z‖ := huniq.unique ⟨hρ_gt, hρ_eq⟩ ⟨hz_gt_outside, hz_witness⟩
    -- Conclude: f(w) = ‖z‖ · (z/‖z‖) = z.
    rw [hρ_normz, hdir_eq]
    field_simp [show (↑‖z‖ : ℂ) ≠ 0 from by exact_mod_cast hz_pos.ne']

/-- **Lemma E**: The external ray map at `c = 2` exists constructively from an
explicit `c = 2` radial-monotonicity seam. -/
theorem external_ray_map_exists_two_via_green_function_of_seam
    (hmono : GreenFunctionStrictMonoAlongRayBasinTwoSeam)
    (hlog_gt_anchor :
      ∀ w : ℂ, 1 < ‖w‖ →
        green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_via_green_function_of_uniquePreimageSeam
    (fun w hw hlog =>
      exists_unique_ray_preimage_green_two_anchor_of_seam hmono w hw hlog)
    hlog_gt_anchor

/-- Current seeded `c = 2` Green inversion constructor. This is the single
swap point for replacing the strict-mono seam assumption with a constructive
theorem at `c = 2`. -/
theorem external_ray_map_exists_two_via_green_function
    (hlog_gt_anchor :
      ∀ w : ℂ, 1 < ‖w‖ →
        green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖) :
    Quadratic.ExternalRayMapData (2 : ℂ) :=
  external_ray_map_exists_two_via_green_function_of_seam
    green_function_strictMono_along_ray_basin_two_axiom_seed
    hlog_gt_anchor

/-- Conditional `c = 2` constructive external-ray map: the Green inversion
construction using anchor-gap existence plus outside-open injectivity. This path
does not use `green_function_strictMono_along_ray_basin_seam`. -/
theorem external_ray_map_exists_two_via_green_function_of_injOn_outside_open
    (hlog_gt_anchor :
      ∀ w : ℂ, 1 < ‖w‖ →
        green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖)
    (h_inj_outside :
      Set.InjOn (Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  have hf_ex : ∀ w : ℂ, 1 < ‖w‖ →
      ∃ ρ : ℝ, ρ > ‖(2 : ℂ)‖ + 2 ∧ green_function (2 : ℂ) ((ρ : ℂ) * (w / ↑‖w‖)) = Real.log ‖w‖ :=
    fun w hw => by
      apply exists_ray_preimage_green_pos
      · rw [norm_div, Complex.norm_real, norm_norm, div_self (by linarith : ‖w‖ ≠ 0)]
      · exact hlog_gt_anchor w hw
  refine ⟨fun w => if hw : 1 < ‖w‖ then
      ↑(Classical.choose (hf_ex w hw)) * (w / ↑‖w‖) else 0, ?_, ?_⟩
  · intro w hw
    simp only [dif_pos hw]
    have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
    have hu : ‖w / ↑‖w‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
    obtain ⟨hρ_gt, hρ_eq⟩ := Classical.choose_spec (hf_ex w hw)
    have hρ_pos : 0 < Classical.choose (hf_ex w hw) := by
      linarith [hρ_gt, norm_nonneg (2 : ℂ)]
    rw [bottcher_map_apply_ray (2 : ℂ) _ hu _ hρ_pos, hρ_eq, Real.exp_log hw_pos]
    exact div_mul_cancel₀ w (by exact_mod_cast hw_pos.ne')
  · intro z hz
    set w := Quadratic.bottcher_map (2 : ℂ) z with hw_def
    have hw_norm : ‖w‖ = Real.exp (green_function (2 : ℂ) z) :=
      norm_bottcher_eq_exp_green (2 : ℂ) z
    have hGz_pos : 0 < green_function (2 : ℂ) z :=
      green_function_pos_on_outside_open (2 : ℂ) z hz
    have hw_gt1 : 1 < ‖w‖ := hw_norm ▸ Real.one_lt_exp_iff.mpr hGz_pos
    have hw_pos : (0 : ℝ) < ‖w‖ := by linarith
    simp only [dif_pos hw_gt1]
    have hu : ‖w / ↑‖w‖‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
    obtain ⟨hρ_gt, hρ_eq⟩ := Classical.choose_spec (hf_ex w hw_gt1)
    have hρ_pos : 0 < Classical.choose (hf_ex w hw_gt1) := by
      linarith [hρ_gt, norm_nonneg (2 : ℂ)]
    set x : ℂ := (((Classical.choose (hf_ex w hw_gt1) : ℝ) : ℂ) * (w / ↑‖w‖))
    have hx_out : ‖x‖ > ‖(2 : ℂ)‖ + 2 := by
      have hx_norm : ‖x‖ = Classical.choose (hf_ex w hw_gt1) := by
        dsimp [x]
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ_pos.le, hu, mul_one]
      linarith [hρ_gt, hx_norm]
    have hx_bottcher : Quadratic.bottcher_map (2 : ℂ) x = w := by
      dsimp [x]
      rw [bottcher_map_apply_ray (2 : ℂ) _ hu _ hρ_pos, hρ_eq, Real.exp_log hw_pos]
      exact div_mul_cancel₀ w (by exact_mod_cast hw_pos.ne')
    have hz_bottcher : Quadratic.bottcher_map (2 : ℂ) z = w := by
      simp [hw_def]
    have hx_eq_z : x = z :=
      h_inj_outside hx_out hz (hx_bottcher.trans hz_bottcher.symm)
    simpa [x] using hx_eq_z

/-- Iterate-left-inverse specialization of the conditional constructive Green
inversion path at `c = 2`. -/
theorem external_ray_map_exists_two_via_green_function_of_iter_left_inverse
    (hlog_gt_anchor :
      ∀ w : ℂ, 1 < ‖w‖ →
        green_function (2 : ℂ)
            (((‖(2 : ℂ)‖ + 2 : ℝ) * (w / ↑‖w‖)) : ℂ) < Real.log ‖w‖)
    (h_left_iter : QuadraticMapIterLeftInverseOnBasin (2 : ℂ)) :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact external_ray_map_exists_two_via_green_function_of_injOn_outside_open
    hlog_gt_anchor
    (bottcher_map_inj_on_outside_open_of_iter_left_inverse (2 : ℂ) h_left_iter)

end GreenFunctionRayInversion

end MLC
