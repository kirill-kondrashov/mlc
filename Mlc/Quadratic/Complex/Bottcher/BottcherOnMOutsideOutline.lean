import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Roadmap for `bottcher_map_deriv_ne_zero_outside`.

Key analytic inputs to formalize:

1. `bottcher_map` is holomorphic on the exterior of a large disk, hence analytic on
   `outside_disk c`.
2. `bottcher_map` is injective on `outside_disk c` (or on a neighborhood of each point).
3. A holomorphic injective map has nonvanishing derivative (conformal).

The following lemmas make these dependencies explicit.
-/

theorem bottcher_map_analytic_on_slit_open
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) U := by
  simpa using (bottcher_map_analyticOnNhd_open c U hUopen hUslit hUbasin)

theorem bottcher_map_inj_on_outside
    (c : ℂ) :
    Set.InjOn (Quadratic.bottcher_map c) (outside_disk c) := by
  intro z hz w hw hzw
  have hz' : Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z :=
    bottcher_theorem_outside c z hz
  have hw' : Quadratic.external_ray_map c (Quadratic.bottcher_map c w) = w :=
    bottcher_theorem_outside c w hw
  have h := congrArg (Quadratic.external_ray_map c) hzw
  simpa [hz', hw'] using h

theorem bottcher_map_deriv_ne_zero_of_inj
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    {z : ℂ} (hz : z ∈ U)
    (hinj : Set.InjOn (Quadratic.bottcher_map c) U)
    (hderiv : deriv (Quadratic.bottcher_map c) z ≠ 0) :
    deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  -- Placeholder until the analytic injectivity-to-nonvanishing lemma is formalized.
  exact hderiv

theorem bottcher_map_deriv_ne_zero_outside
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    {z : ℂ} (hz : z ∈ U)
    (hinj : Set.InjOn (Quadratic.bottcher_map c) U)
    (hderiv : deriv (Quadratic.bottcher_map c) z ≠ 0) :
    deriv (Quadratic.bottcher_map c) z ≠ 0 := by
  exact bottcher_map_deriv_ne_zero_of_inj c U hUopen hUslit hUbasin hz hinj hderiv

theorem bottcher_left_inv_outside_of_local
    (c : ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hUslit : U ⊆ slit_orbit c)
    (hUbasin : U ⊆ Quadratic.basin_of_infinity c)
    (z : ℂ) (hzU : z ∈ U) (hderiv : deriv (Quadratic.bottcher_map c) z ≠ 0)
    (h_eq : ∀ᶠ y in 𝓝 (Quadratic.bottcher_map c z),
      Quadratic.external_ray_map c y =
        external_ray_map_local c U hUopen hUslit hUbasin z hzU hderiv y) :
    Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z := by
  have hlocal :
      ∀ᶠ x in 𝓝 z,
        external_ray_map_local c U hUopen hUslit hUbasin z hzU hderiv
          (Quadratic.bottcher_map c x) = x :=
    external_ray_map_local_left_inverse c U hUopen hUslit hUbasin z hzU hderiv
  have hcontOn : ContinuousOn (Quadratic.bottcher_map c) U :=
    (bottcher_map_differentiableOn_open c U hUopen hUslit hUbasin).continuousOn
  have hcont : ContinuousAt (Quadratic.bottcher_map c) z :=
    hcontOn.continuousAt (hUopen.mem_nhds hzU)
  have hcomp :
      ∀ᶠ x in 𝓝 z,
        Quadratic.external_ray_map c (Quadratic.bottcher_map c x) =
          external_ray_map_local c U hUopen hUslit hUbasin z hzU hderiv
            (Quadratic.bottcher_map c x) := by
    let S : Set ℂ :=
      {y | Quadratic.external_ray_map c y =
        external_ray_map_local c U hUopen hUslit hUbasin z hzU hderiv y}
    have hpre : (Quadratic.bottcher_map c) ⁻¹' S ∈ 𝓝 z := by
      refine hcont.preimage_mem_nhds ?_
      exact (Filter.eventually_iff).1 h_eq
    have hpre' :
        {x | Quadratic.external_ray_map c (Quadratic.bottcher_map c x) =
          external_ray_map_local c U hUopen hUslit hUbasin z hzU hderiv
            (Quadratic.bottcher_map c x)} ∈ 𝓝 z := by
      simpa [S, Set.preimage] using hpre
    exact (Filter.eventually_iff).2 hpre'
  have hlocal' :
      ∀ᶠ x in 𝓝 z,
        Quadratic.external_ray_map c (Quadratic.bottcher_map c x) = x := by
    exact (hcomp.and hlocal).mono (by intro x hx; exact (hx.1.trans hx.2))
  have hmem : {x | Quadratic.external_ray_map c (Quadratic.bottcher_map c x) = x} ∈ 𝓝 z :=
    (Filter.eventually_iff).1 hlocal'
  rcases mem_nhds_iff.1 hmem with ⟨s, hs, _hsopen, hzs⟩
  exact hs hzs

end MLC
