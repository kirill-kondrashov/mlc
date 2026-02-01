import Mlc.Quadratic.Complex.BottcherOnMTheory

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Outline: proving `bottcher_map_inj_on_outside`.

This file records the minimal analytic/dynamical lemmas needed to replace the
axiom `bottcher_map_inj_on_outside` with a proof. No axioms are introduced here.

Roadmap (target: injectivity on `outside_disk c`):

1. Analyticity near infinity.
   - Show `bottcher_map` is holomorphic on a neighborhood of the exterior.
   - Suggested lemma:
     `bottcher_map_analytic_on_outside :
        AnalyticOnNhd ℂ (Quadratic.bottcher_map c) (outside_disk c)`

2. Asymptotic normalization at infinity.
   - Prove the Böttcher coordinate has the standard normalization:
     `tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 1)`
   - This pins down the degree and rules out nontrivial deck transformations.

3. Nonvanishing derivative on the exterior.
   - Use the conjugacy `φ(f(z)) = φ(z)^2` and the asymptotics to show:
     `deriv (Quadratic.bottcher_map c) z ≠ 0` for `z ∈ outside_disk c`.
   - Alternatively, derive local injectivity from a local inverse
     `external_ray_map_local` on the exterior.

4. Properness / degree-one argument.
   - Show `bottcher_map` is proper on the exterior and has degree 1.
   - Combined with local injectivity, this yields global injectivity:
     `Set.InjOn (Quadratic.bottcher_map c) (outside_disk c)`.

5. Range characterization (optional, but standard):
   - `‖bottcher_map c z‖ > 1` for `z` in the exterior, and surjectivity onto
     `{w | 1 < ‖w‖}`. This also yields the preimage inclusion axiom.

Once the above lemmas are formalized, the axioms
`bottcher_map_inj_on_outside` and `bottcher_map_preimage_exterior_subset_outside`
can be removed, and `bottcher_theorem_outside` becomes a direct corollary.
-/

lemma bottcher_map_norm_gt_one_of_outside (c : ℂ) {z : ℂ} (hz : z ∈ outside_disk c) :
    1 < ‖Quadratic.bottcher_map c z‖ := by
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    outside_disk_subset_quadratic_basin c hz
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    green_function_pos_of_basin c z hz_basin
  exact bottcher_map_norm_gt_one_of_basin c z hz_basin hpos

lemma bottcher_map_norm_gt_one_implies_basin (c : ℂ) {z : ℂ}
    (hz : 1 < ‖Quadratic.bottcher_map c z‖) :
    z ∈ Quadratic.basin_of_infinity c := by
  have hnorm' : ‖Quadratic.bottcher_map c z‖ =
      Real.exp (MLC.Quadratic.green_function c z) :=
    Quadratic.norm_bottcher_eq_exp_green c z
  have hpos : 0 < MLC.Quadratic.green_function c z := by
    have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
      simpa [hnorm'] using hz
    exact (Real.one_lt_exp_iff).1 hgt
  have hz' : z ∉ MLC.Quadratic.K c :=
    (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).1 hpos
  have : z ∈ (MLC.Quadratic.K c)ᶜ := by
    simpa [Set.mem_compl_iff] using hz'
  simpa [Quadratic.basin_eq_compl_K c] using this

def bottcher_preimage_exterior_outside_cond (c : ℂ) : Prop :=
  ∀ z, 1 < ‖Quadratic.bottcher_map c z‖ → z ∈ outside_disk c

lemma bottcher_map_preimage_exterior_subset_outside_of
    (c : ℂ) (hcond : bottcher_preimage_exterior_outside_cond c) :
    (Quadratic.bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c := by
  intro z hz
  have : 1 < ‖Quadratic.bottcher_map c z‖ := by
    simpa [Set.preimage] using hz
  exact hcond z this

def bottcher_basin_subset_outside_cond (c : ℂ) : Prop :=
  ∀ z, z ∈ Quadratic.basin_of_infinity c → z ∈ outside_disk c

lemma bottcher_preimage_exterior_outside_cond_of_basin
    (c : ℂ) (hbasin : bottcher_basin_subset_outside_cond c) :
    bottcher_preimage_exterior_outside_cond c := by
  intro z hz
  exact hbasin z (bottcher_map_norm_gt_one_implies_basin c hz)

lemma bottcher_map_analytic_on_outside_of_slit (c : ℂ)
    (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  have hUopen : IsOpen {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
    simpa using (isOpen_lt continuous_const continuous_norm)
  have hUbasin : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ Quadratic.basin_of_infinity c := by
    intro z hz
    have hz' : z ∈ outside_disk c := by
      simpa [outside_disk] using (le_of_lt hz)
    exact outside_disk_subset_quadratic_basin c hz'
  exact bottcher_map_analyticOnNhd_open c _ hUopen hslit hUbasin

def atInfinity : Filter ℂ :=
  Filter.comap (fun z : ℂ => ‖z‖) atTop

def bottcher_normalized_at_infty (c : ℂ) : Prop :=
  Tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 (1 : ℂ))

lemma bottcher_normalized_at_infty_implies_nontrivial (c : ℂ)
    (hnorm : bottcher_normalized_at_infty c) :
    Tendsto (fun z => (Quadratic.bottcher_map c z) / z) atInfinity (𝓝 (1 : ℂ)) :=
  hnorm

def bottcher_deriv_nonzero_on_outside (c : ℂ) : Prop :=
  ∀ z, z ∈ outside_disk c → deriv (Quadratic.bottcher_map c) z ≠ 0

end MLC
