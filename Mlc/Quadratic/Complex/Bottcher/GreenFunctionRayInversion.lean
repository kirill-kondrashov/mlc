import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.ParaPuzzleBasis

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
- [ ] Lemma C: `green_function_strictMono_along_ray` — core technical lemma (sorry).
- [ ] Lemma D: `exists_unique_ray_preimage_green` — needs Lemma C + IVT (sorry).
- [ ] Lemma E: `external_ray_map_two_constructive` — needs Lemma D (sorry).
-/

namespace MLC

open Quadratic Complex Topology Set Filter Metric

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

/-! ## Lemma C: Strict monotonicity along radial rays (core technical lemma) -/

/-- **Lemma C** [sorry]: The Green function is strictly increasing along each radial ray
in the outside-open set. For fixed unit vector `u : ℂ` and `t₁ < t₂` both `> ‖c‖ + 2`:
`green_function c (t₁ * u) < green_function c (t₂ * u)`.

Proof strategy: uses the harmonic maximum principle applied to the domain bounded by the
level sets of G_c, combined with the fact that G_c → 0 on ∂K_c and G_c → ∞ at ∞.
This is the core technical lemma requiring harmonic analysis not yet in Mathlib. -/
lemma green_function_strictMono_along_ray (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {t₁ t₂ : ℝ} (ht₁ : t₁ > ‖c‖ + 2) (ht₂ : t₁ < t₂) :
    Quadratic.green_function c (t₁ * u) < Quadratic.green_function c (t₂ * u) := by
  sorry

/-! ## Lemma D: Unique ray preimage of each Green function value -/

/-- **Lemma D** [sorry]: For each unit vector `u : ℂ` and each Green value `t` exceeding
the minimum Green value on the ray, there is a unique `ρ > ‖c‖ + 2` with
`green_function c (ρ * u) = t`.

Proof strategy: existence from Lemma B (IVT along the ray) + uniqueness from Lemma C. -/
lemma exists_unique_ray_preimage_green (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ)
    (ht : t > Quadratic.green_function c ((‖c‖ + 2 : ℝ) * u)) :
    ∃! ρ : ℝ, ρ > ‖c‖ + 2 ∧ Quadratic.green_function c ((ρ : ℂ) * u) = t := by
  sorry

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
  preimage by Lemma C is `z` itself. ✓ -/
theorem external_ray_map_exists_two_via_green_function :
    Quadratic.ExternalRayMapData (2 : ℂ) := by
  sorry

end GreenFunctionRayInversion

end MLC
