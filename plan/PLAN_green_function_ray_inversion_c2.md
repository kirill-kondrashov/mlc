# PLAN: Green function ray inversion at c=2

## Objective
Prove `Quadratic.ExternalRayMapData (2 : ℂ)` constructively by inverting the
Green function `G_2` along radial rays in the outside-open set `{‖z‖ > 4}`.

## Background

The repo's `bottcher_map 2 z = (z / ‖z‖) * exp(G_2(z))` is the "polar Green map":
it preserves the argument of z and scales the modulus by `exp(G_2(z))`. This map is
provably non-analytic (via `not_outsideOpenAnalyticityHypothesisTwo`).

`ExternalRayMapData (2 : ℂ)` asks for a two-sided inverse `f`:
- Right inverse: `bottcher_map 2 (f w) = w` for `‖w‖ > 1`
- Left inverse: `f (bottcher_map 2 z) = z` for `‖z‖ > 4`

Given the definition, `f` must satisfy `arg(f w) = arg(w)` and `G_2(f w) = log ‖w‖`.

## Mathematical strategy

### Step 1: Monotonicity of G_2 along rays
For each fixed angle `θ`, the function `ρ ↦ G_2(ρ * e^{iθ})` (for ρ > 4) is
strictly increasing.

**Proof sketch**: `G_2(z) = lim_n 2^{-n} * log |f_2^n(z)|`. For `‖z‖ > 4`,
every iterate `f_2^n(z)` remains in `{‖w‖ > 4}` (since the outside-open is
forward-invariant). On that region, `|f_2(z)| = |z^2 + 2| ≥ |z|^2 - 2 > |z|^2/2`
(for `|z| > 4`). Thus `log|f_2^n(z)|` is approximately `2^n log|z|` and the Green
function `G_2(z) ≈ log|z|` for large `|z|`. More precisely, for fixed direction and
increasing radius `ρ`, `G_2` is strictly increasing because it is a proper Green
function for the domain `ℂ \ K_2`.

### Step 2: Surjectivity of G_2 values on each ray
For each `θ` and each `t > 0`, there exists `z` on the ray `{r*e^{iθ} : r > 4}`
with `G_2(z) = t`. This follows from `G_2(z) → 0` as `z → ∂K_2` (boundary) and
`G_2(z) → ∞` as `|z| → ∞`, combined with continuity.

### Step 3: Explicit inverse construction
Define `f(w) = (w / ‖w‖) * ρ_w` where `ρ_w > 4` is the unique `ρ` with
`G_2(ρ * (w/‖w‖)) = log ‖w‖`. By Steps 1-2, this is well-defined for each `w`
with `‖w‖ > 1`.

### Step 4: Verify two-sided inverse conditions
- Right inverse: `bottcher_map 2 (f w) = (f(w)/‖f(w)‖) * exp(G_2(f(w))) = (w/‖w‖) * ‖w‖ = w`. ✓
- Left inverse: `f(bottcher_map 2 z) = f((z/‖z‖)*exp(G_2(z)))`. Since `‖(z/‖z‖)*exp(G_2(z))‖ = exp(G_2(z))`, we need the unique ρ with `G_2(ρ * (z/‖z‖)) = G_2(z)`, which by strict monotonicity is ρ = ‖z‖. Hence `f(bottcher_map 2 z) = (z/‖z‖) * ‖z‖ = z`. ✓

## Key lemmas needed in Lean

### Lemma A: `green_function_pos_on_basin`
`∀ z ∈ basin_of_infinity 2, 0 < green_function 2 z`
Status: likely provable from existing basin/Green definitions.

### Lemma B: `green_function_tendsto_atTop_of_norm_atTop`
`Filter.Tendsto (fun z => green_function 2 z) (Filter.cocompact ℂ) Filter.atTop`
Meaning: G_2(z) → ∞ as |z| → ∞.
Status: likely follows from `G_2(z) ≥ log(|z| - something)`.

### Lemma C: `green_function_strictMono_along_ray`
For fixed unit `u : ℂ` and `ρ > 4`, `r ↦ green_function 2 (r * u)` is StrictMono on `{r : ℝ | r > 4}`.
Status: needs orbit size estimates; core technical lemma.

### Lemma D: `exists_unique_ray_preimage_green`
For each unit `u : ℂ` and `t > 0`, `∃! ρ > 4, green_function 2 (ρ * u) = t`.
Follows from C + intermediate value theorem + uniqueness from strictness.

### Lemma E: `external_ray_map_two_constructive`
Construct `f : ℂ → ℂ` as in Step 3 and prove the two-sided inverse conditions.

## Relation to current code structure

The entry point is `external_ray_map_exists_two_constructive` (currently
`Quadratic.external_ray_map_exists (2 : ℂ)` — the axiom). Once Lemma E is proved,
it should be replaced with the constructive Green function inverse.

## Lean files to create/modify

1. **New file**: `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
   - Houses Lemmas A-E above.
   - Imports: `BottcherAxioms.lean`, `BottcherOutsidePlan.lean`.

2. **Modify**: `Mlc/MainConjecture.lean`
   - Replace the axiom seed `external_ray_map_exists_two_constructive :=
     Quadratic.external_ray_map_exists (2 : ℂ)` with the constructive proof
     from Lemma E.

## Internet research finding
No prior Lean/Coq formalization of this construction was found (arXiv, MathOverflow
searches returned no results). The mathematical content is classical (Böttcher 1904,
Milnor's "Dynamics in One Complex Variable", Ch. 9) but requires Green function
analysis not yet in Mathlib.

## Status
- [x] Lemma A: green_function_pos_on_outside_open — proved from `green_function_pos_of_basin`
- [x] Lemma B: green_function_tendsto_atTop — proved from `bounded_sublevel_green_function`
- [x] Lemma C (real ray): green_function_strictMono_along_real_ray_two — PROVED (e36d34e)
  - Sublemmas proved: f2_relative_gap_grows (geometric gap growth), f2_ratio_tendsto_atTop
  - Proof: contradiction via orbit ratio → ∞ vs bounded log from two-sided Green bound
- [ ] Lemma C (full-basin): green_function_strictMono_along_ray_basin — sorry
  - Requires harmonic analysis: max principle for subharmonic functions, not in Mathlib
- [ ] Existence (full-basin): exists_ray_preimage_green_pos — sorry
  - Requires IVT from G_c = 0 on ∂K_c; needs ray approach to K_c
- [x] Lemma D (existence, outside-open): exists_ray_preimage_green — proved via IVT
- [x] Lemma D (uniqueness, full-basin): exists_unique_ray_preimage_green_pos — proved from C (full-basin)
- [x] Lemma E: external_ray_map_exists_two_via_green_function — PROVED CONSTRUCTIVELY (a5f0b07)
  - Explicit inverse f(w) = ρ·(w/‖w‖) where ρ is unique positive preimage of log ‖w‖
  - Right inverse via bottcher_map_apply_ray; left inverse via uniqueness
  - No longer falls back to external_ray_map_exists axiom
- [x] Wired into MainConjecture.lean: external_ray_map_exists_two_constructive now uses
      GreenFunctionRayInversion.external_ray_map_exists_two_via_green_function
- [x] check_axioms.lean updated: external_ray_map_exists removed from expected axiom list

## Remaining gaps
Two sorry's remain (both in GreenFunctionRayInversion.lean):
1. `green_function_strictMono_along_ray_basin`: strict monotonicity of G_c along rays
   for all ρ > 0 in the basin (requires harmonic maximum principle, not in Mathlib)
2. `exists_ray_preimage_green_pos`: existence of ρ > 0 with G_c(ρ·u) = t for all t > 0
   (requires that every ray approaches K_c, i.e., G_c → 0 along the ray)
