import Mlc.Quadratic.Complex.Bottcher.BottcherCore
import Mlc.Quadratic.Complex.ParaPuzzleBasis
import Mlc.Quadratic.Complex.Axioms
import Mathlib.Topology.Order.IntermediateValue

/-!
# Legacy radial-proxy external-ray construction for `c ∈ M`

This file proves `external_ray_map_data_of_mandelbrot`, the exact statement of the
former `external_ray_map_exists` axiom restricted to its true domain
`c ∈ MandelbrotSet`, using only Lean-core axioms plus the radial
strict-monotonicity seam
(`green_function_strictMono_along_ray_basin_seam`). It is deliberately placed
**upstream** of `BottcherAxioms` so that the compatibility
`external_ray_map` / `extended_ray_map` definitions can be available without an
additional existence axiom. This legacy radial-proxy construction is not used
by the checked `MLC.mlc_conjecture` path.

The construction is elementary:
* For `c ∈ M` the critical value `0 ∈ K c`, so `green_function c 0 = 0`; every origin ray
  sweeps `G` over `(0, ∞)` and IVT anchored at `ρ = 0` gives surjectivity of the radial
  proxy onto `{‖w‖ > 1}` (no monotonicity needed).
* Injectivity of the radial proxy on the far-exterior `{‖z‖ > ‖c‖ + 2}` follows from the
  strict-mono ray seam.
* The `ExternalRayMapData` package (right-inverse on `{‖w‖ > 1}` + left-inverse on the
  outside region) is assembled directly, avoiding the false Böttcher functional equation.

All escape/basin helpers are reproved locally so the file depends on nothing downstream of
`BottcherAxioms`.
-/

namespace MLC

namespace GreenRayDischarge

open Quadratic Complex Topology Set Filter Metric Real

/-! ## Elementary escape estimates (reproved upstream) -/

private theorem qm_norm_lower (c z : ℂ) :
    ‖quadratic_map c z‖ ≥ ‖z‖ ^ 2 - ‖c‖ := by
  have h : ‖z ^ 2‖ ≤ ‖quadratic_map c z‖ + ‖c‖ := by
    have h' := norm_add_le (quadratic_map c z) (-c)
    simpa [quadratic_map, add_comm, add_left_comm, add_assoc] using h'
  have h' : ‖z ^ 2‖ - ‖c‖ ≤ ‖quadratic_map c z‖ := sub_le_iff_le_add.mpr h
  have hz : ‖z ^ 2‖ = ‖z‖ ^ 2 := by simp [pow_two]
  simpa [hz] using h'

private theorem qm_norm_ge_add_one (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    ‖quadratic_map c z‖ ≥ ‖z‖ + 1 := by
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖quadratic_map c z‖ := qm_norm_lower c z
  have hy : ‖c‖ ≤ ‖z‖ - 2 := by nlinarith
  have h2a : ‖z‖ ^ 2 - (‖z‖ - 2) ≤ ‖z‖ ^ 2 - ‖c‖ := by nlinarith [hy]
  have h2b : ‖z‖ + 1 ≤ ‖z‖ ^ 2 - (‖z‖ - 2) := by
    have hsq : 0 ≤ (‖z‖ - 1) ^ 2 := by nlinarith
    nlinarith [hsq]
  exact le_trans (le_trans h2b h2a) h1

private theorem iter_qm_norm_ge_add (c z : ℂ) :
    ∀ n, ‖z‖ ≥ ‖c‖ + 2 → ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hz
      have h0 : ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := ih hz
      have h_ge : ‖(quadratic_map c)^[n] z‖ ≥ ‖c‖ + 2 := by
        have h1 : ‖c‖ + 2 ≤ ‖z‖ := by nlinarith
        have hbase : ‖z‖ ≤ ‖z‖ + n := by nlinarith
        exact le_trans h1 (le_trans hbase h0)
      have h1 : ‖quadratic_map c ((quadratic_map c)^[n] z)‖ ≥
          ‖(quadratic_map c)^[n] z‖ + 1 := qm_norm_ge_add_one c _ h_ge
      have h2 : ‖(quadratic_map c)^[n] z‖ + 1 ≥ ‖z‖ + (n + 1) := by nlinarith
      have h3 : ‖(quadratic_map c)^[n.succ] z‖ ≥ ‖z‖ + (n + 1) := by
        rw [Function.iterate_succ']
        simpa [Function.comp_apply] using le_trans h2 h1
      simpa using h3

private theorem large_norm_tendsto_infty (c z : ℂ) (hz : ‖z‖ ≥ ‖c‖ + 2) :
    Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
  have hmono : ∀ n, ‖(quadratic_map c)^[n] z‖ ≥ ‖z‖ + n := fun n =>
    iter_qm_norm_ge_add c z n hz
  have h1 : Tendsto (fun n : ℕ => ‖z‖ + n) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono (fun n => by nlinarith [norm_nonneg z]) hnat
  exact tendsto_atTop_mono hmono h1

theorem outside_open_subset_basin (c : ℂ) :
    {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ Quadratic.basin_of_infinity c := by
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  exact large_norm_tendsto_infty c z (le_of_lt hz)

/-! ## Green-function positivity helpers -/

theorem green_function_pos_of_basin (c z : ℂ)
    (hz : z ∈ Quadratic.basin_of_infinity c) : 0 < green_function c z := by
  have hz'' : z ∉ MLC.Quadratic.K c := by
    have := (Quadratic.basin_eq_compl_K c) ▸ hz
    simpa [Set.mem_compl_iff] using this
  exact (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).2 hz''

theorem green_function_pos_on_outside_open (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    0 < green_function c z :=
  green_function_pos_of_basin c z (outside_open_subset_basin c hz)

/-! ## Radial strict monotonicity (wraps the seam axiom) -/

theorem green_function_strictMono_along_ray_basin (c u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function c ((ρ₁ : ℂ) * u)) :
    green_function c ((ρ₁ : ℂ) * u) < green_function c ((ρ₂ : ℂ) * u) :=
  Quadratic.green_function_strictMono_along_ray_basin_seam c u hu hρ₁ h12 hG

/-! ## Surjectivity of the radial proxy onto `{‖w‖ > 1}` for `c ∈ M` -/

theorem exists_ray_preimage_green_of_mandelbrot (c : ℂ) (hc : c ∈ MandelbrotSet)
    (u : ℂ) (hu : ‖u‖ = 1) (t : ℝ) (ht : 0 < t) :
    ∃ ρ : ℝ, 0 < ρ ∧ green_function c ((ρ : ℂ) * u) = t := by
  set g := fun ρ : ℝ => green_function c ((ρ : ℂ) * u) with hg_def
  have hg_cont : Continuous g :=
    (continuous_green_function c).comp (Complex.continuous_ofReal.mul continuous_const)
  have hg0 : g 0 = 0 := by
    have h0K : (0 : ℂ) ∈ K c := hc
    simp only [hg_def, Complex.ofReal_zero, zero_mul]
    exact (green_function_eq_zero_iff_mem_K c 0).2 h0K
  obtain ⟨R₀, hR₀_pos, hR₀_ge⟩ : ∃ R₀ : ℝ, 0 < R₀ ∧ g R₀ ≥ t := by
    have hbdd := bounded_sublevel_green_function c t
    rw [isBounded_iff_forall_norm_le] at hbdd
    obtain ⟨R, hR⟩ := hbdd
    refine ⟨max 1 (R + 1), by linarith [le_max_left 1 (R + 1)], ?_⟩
    by_contra h
    push_neg at h
    have hmem : (↑(max 1 (R + 1)) * u : ℂ) ∈ {z : ℂ | green_function c z < t} := by
      simpa [hg_def] using h
    have hle := hR _ hmem
    have hnorm : ‖(↑(max 1 (R + 1)) * u : ℂ)‖ > R := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg, hu, mul_one]
      · linarith [le_max_right 1 (R + 1)]
      · exact le_trans (by norm_num) (le_max_left _ _)
    linarith
  have hIVT : ∃ ρ ∈ Set.Icc (0 : ℝ) R₀, g ρ = t :=
    intermediate_value_Icc hR₀_pos.le hg_cont.continuousOn
      ⟨by rw [hg0]; exact ht.le, hR₀_ge⟩
  obtain ⟨ρ, ⟨hρ_ge, _⟩, hρ_eq⟩ := hIVT
  refine ⟨ρ, ?_, hρ_eq⟩
  rcases lt_or_eq_of_le hρ_ge with hlt | rfl
  · exact hlt
  · rw [hg0] at hρ_eq; exact absurd hρ_eq.symm ht.ne'

theorem surjOn_proxy_bottcher_map_of_mandelbrot (c : ℂ) (hc : c ∈ MandelbrotSet) :
    ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Quadratic.proxy_bottcher_map c z = w := by
  intro w hw
  have hw_pos : (0 : ℝ) < ‖w‖ := lt_trans zero_lt_one hw
  set u : ℂ := w / (‖w‖ : ℂ) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, norm_norm, div_self hw_pos.ne']
  have ht : 0 < Real.log ‖w‖ := Real.log_pos hw
  obtain ⟨ρ, hρ_pos, hρ_eq⟩ :=
    exists_ray_preimage_green_of_mandelbrot c hc u hu (Real.log ‖w‖) ht
  refine ⟨(ρ : ℂ) * u, ?_⟩
  rw [Quadratic.proxy_bottcher_map_apply_ray c u hu ρ hρ_pos, hρ_eq, Real.exp_log hw_pos,
    hu_def]
  exact div_mul_cancel₀ w (by exact_mod_cast hw_pos.ne')

/-! ## Far-exterior injectivity of the radial proxy (general `c`) -/

theorem injOn_proxy_bottcher_map_outside_open (c : ℂ) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} := by
  intro z₁ hz₁ z₂ hz₂ hEq
  simp only [Set.mem_setOf_eq] at hz₁ hz₂
  have hnp₁ : (0 : ℝ) < ‖z₁‖ := by linarith [norm_nonneg c]
  have hnp₂ : (0 : ℝ) < ‖z₂‖ := by linarith [norm_nonneg c]
  have hz₁0 : z₁ ≠ 0 := fun h => by rw [h, norm_zero] at hnp₁; exact lt_irrefl _ hnp₁
  have hz₂0 : z₂ ≠ 0 := fun h => by rw [h, norm_zero] at hnp₂; exact lt_irrefl _ hnp₂
  have hnorm_eq : Real.exp (green_function c z₁) = Real.exp (green_function c z₂) := by
    have := congrArg norm hEq
    rwa [Quadratic.norm_bottcher_eq_exp_green, Quadratic.norm_bottcher_eq_exp_green] at this
  have hG_eq : green_function c z₁ = green_function c z₂ := by
    have := congrArg Real.log hnorm_eq
    rwa [Real.log_exp, Real.log_exp] at this
  have hproxy₁ : Quadratic.proxy_bottcher_map c z₁ =
      (z₁ / (‖z₁‖ : ℂ)) * (Real.exp (green_function c z₁) : ℂ) := by
    simp [Quadratic.proxy_bottcher_map, Quadratic.polar_green_map, hz₁0]
  have hproxy₂ : Quadratic.proxy_bottcher_map c z₂ =
      (z₂ / (‖z₂‖ : ℂ)) * (Real.exp (green_function c z₂) : ℂ) := by
    simp [Quadratic.proxy_bottcher_map, Quadratic.polar_green_map, hz₂0]
  have hexp_ne : ((Real.exp (green_function c z₁) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_pos _).ne'
  have hdir : z₁ / (‖z₁‖ : ℂ) = z₂ / (‖z₂‖ : ℂ) := by
    have hEq' : (z₁ / (‖z₁‖ : ℂ)) * (Real.exp (green_function c z₁) : ℂ) =
        (z₂ / (‖z₂‖ : ℂ)) * (Real.exp (green_function c z₁) : ℂ) := by
      rw [← hproxy₁, hEq, hproxy₂, hG_eq]
    exact mul_right_cancel₀ hexp_ne hEq'
  set u : ℂ := z₁ / (‖z₁‖ : ℂ) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, norm_norm, div_self hnp₁.ne']
  have hcast₁ : ((‖z₁‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnp₁.ne'
  have hcast₂ : ((‖z₂‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnp₂.ne'
  have hz₁_ray : z₁ = ((‖z₁‖ : ℝ) : ℂ) * u := by
    rw [hu_def, mul_comm, div_mul_cancel₀ _ hcast₁]
  have hz₂_ray : z₂ = ((‖z₂‖ : ℝ) : ℂ) * u := by
    rw [hdir, mul_comm, div_mul_cancel₀ _ hcast₂]
  rcases lt_trichotomy ‖z₁‖ ‖z₂‖ with hlt | heq | hgt
  · exfalso
    have hG₁ray : 0 < green_function c (((‖z₁‖ : ℝ) : ℂ) * u) := by
      rw [← hz₁_ray]; exact green_function_pos_on_outside_open c z₁ hz₁
    have := green_function_strictMono_along_ray_basin c u hu hnp₁ hlt hG₁ray
    rw [← hz₁_ray, ← hz₂_ray, hG_eq] at this
    exact lt_irrefl _ this
  · rw [hz₁_ray, hz₂_ray, heq]
  · exfalso
    have hG₂ray : 0 < green_function c (((‖z₂‖ : ℝ) : ℂ) * u) := by
      rw [← hz₂_ray]; exact green_function_pos_on_outside_open c z₂ hz₂
    have := green_function_strictMono_along_ray_basin c u hu hnp₂ hgt hG₂ray
    rw [← hz₁_ray, ← hz₂_ray, hG_eq] at this
    exact lt_irrefl _ this

/-! ## Discharge of the external-ray-map existence axiom for `c ∈ M` -/

/-- **Discharge of `external_ray_map_exists` for `c ∈ M`.**  Assembles the far-exterior
injectivity and full-exterior surjectivity of the radial proxy into the root-facing
external-ray data package, directly (bypassing any Böttcher functional-equation
hypothesis).  Depends only on the strict-mono ray seam. -/
theorem external_ray_map_data_of_mandelbrot (c : ℂ) (hc : c ∈ MandelbrotSet) :
    Quadratic.ExternalRayMapData c := by
  classical
  have h_surj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Quadratic.proxy_bottcher_map c z = w :=
    surjOn_proxy_bottcher_map_of_mandelbrot c hc
  have h_inj_outside :
      Set.InjOn (Quadratic.proxy_bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
    injOn_proxy_bottcher_map_outside_open c
  have h_norm_outside :
      ∀ z : ℂ, ‖z‖ > ‖c‖ + 2 → 1 < ‖Quadratic.proxy_bottcher_map c z‖ := by
    intro z hz
    rw [Quadratic.norm_bottcher_eq_exp_green]
    exact Real.one_lt_exp_iff.mpr (green_function_pos_on_outside_open c z hz)
  refine ⟨fun w =>
      if hw : 1 < ‖w‖ then
        (if hV : ∃ z : ℂ, ‖z‖ > ‖c‖ + 2 ∧ Quadratic.proxy_bottcher_map c z = w then
          Classical.choose hV
         else Classical.choose (h_surj w hw))
      else 0, ?_, ?_⟩
  · intro w hw
    simp only [dif_pos hw]
    by_cases hV : ∃ z : ℂ, ‖z‖ > ‖c‖ + 2 ∧ Quadratic.proxy_bottcher_map c z = w
    · rw [dif_pos hV]; exact (Classical.choose_spec hV).2
    · rw [dif_neg hV]; simpa using Classical.choose_spec (h_surj w hw)
  · intro z hz
    have hw : 1 < ‖Quadratic.proxy_bottcher_map c z‖ := h_norm_outside z hz
    have hV : ∃ u : ℂ, ‖u‖ > ‖c‖ + 2 ∧
        Quadratic.proxy_bottcher_map c u = Quadratic.proxy_bottcher_map c z := ⟨z, hz, rfl⟩
    simp only [dif_pos hw, dif_pos hV]
    exact h_inj_outside (Classical.choose_spec hV).1 hz (Classical.choose_spec hV).2

end GreenRayDischarge

end MLC
