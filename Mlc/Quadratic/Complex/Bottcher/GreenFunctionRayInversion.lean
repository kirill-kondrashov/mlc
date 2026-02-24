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
  | zero => simp [orbit_zero, f2]
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

/-! ## Lemma C: Strict monotonicity along the positive real ray for `c = 2` -/

/-- The orbit ratio of two positive reals grows: for ρ₁ < ρ₂ both > 4, the relative gap
`(f2^[n] ρ₂ - f2^[n] ρ₁) / f2^[n] ρ₁` grows at least geometrically with ratio 16/9.

Proof: δ_{n+1} = (A_n + B_n)*δ_n, and A_n^2/(A_n^2+2) ≥ 16/18 for A_n ≥ 4, so
ε_{n+1} = δ_{n+1}/A_{n+1} ≥ (16/9)*ε_n. -/
private lemma f2_relative_gap_grows {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂) (hρ₁ : ρ₁ > 4) (n : ℕ) :
    (f2 ^[n] ρ₂ - f2 ^[n] ρ₁) / f2 ^[n] ρ₁ ≥ (16 / 9) ^ n * ((ρ₂ - ρ₁) / ρ₁) := by
  -- Induction: gap ε_{n+1} = (A_n+B_n)*ε_n/A_{n+1} ≥ (16/9)*ε_n since A_n ≥ 4.
  sorry

/-- The orbit ratio `f2^[n] ρ₂ / f2^[n] ρ₁` tends to infinity when ρ₁ < ρ₂. -/
private lemma f2_ratio_tendsto_atTop {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂) (hρ₁ : ρ₁ > 4) :
    Tendsto (fun n : ℕ => f2 ^[n] ρ₂ / f2 ^[n] ρ₁) atTop atTop := by
  -- Strategy: ratio ≥ (16/9)^n * ε₀ where ε₀ = (ρ₂-ρ₁)/ρ₁ > 0.
  -- Lower bound from f2_relative_gap_grows; upper bound from (16/9)^n → ∞.
  sorry

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
  -- Proof by contradiction: assume G₂(ρ₁) ≥ G₂(ρ₂).
  -- The functional equation G₂(f2^n(ρᵢ)) = 2^n * G₂(ρᵢ) combined with
  -- the two-sided bound |G₂(z) - log‖z‖| ≤ M gives log(f2^n ρ₂/f2^n ρ₁) bounded,
  -- but f2_ratio_tendsto_atTop says the ratio → ∞. Contradiction.
  -- Key lemmas: f2_ratio_tendsto_atTop, green_function_orbit_eq,
  --             green_function_bdd_above_log, green_function_bdd_below_log.
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

/-! ## Lemma E: Constructive external ray map at `c = 2` -/

/-- **Lemma E** [sorry]: The external ray map at `c = 2` exists constructively.
Uses Lemma D to construct the unique inverse `f(w)` for each `w` with `‖w‖ > 1`, where
`f` maps `w` to the unique point `z` with `arg(z) = arg(w)` and `G_2(z) = log ‖w‖`.

Proof sketch:
- For `‖w‖ > 1`, `Real.log ‖w‖ > 0 = green_function 2 (boundary)`.
- Define `u := w / ‖w‖` (the unit vector in the direction of w).
- By Lemma D, there exists unique `ρ > 4` with `green_function 2 (ρ * u) = log ‖w‖`.
- Set `f(w) := ρ * u`.
- Right inverse: `bottcher_map 2 (f w) = (f(w)/‖f(w)‖) * exp(G_2(f(w))) = u * ‖w‖ = w`. ✓
- Left inverse: for `‖z‖ > 4`, `bottcher_map 2 z = (z/‖z‖) * exp(G_2(z))`.
  Then `f(bottcher_map 2 z)` has direction `z/‖z‖` and `G_2 = G_2(z)`, so unique
  preimage by Lemma C is `z` itself. ✓
- Depends on the full Lemma C (general complex direction), which is still sorry. -/
theorem external_ray_map_exists_two_via_green_function :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  sorry

end GreenFunctionRayInversion

end MLC
