import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinCoordinate
import Mlc.Quadratic.Complex.Bottcher.BottcherCpowSlit

open MLC MLC.Quadratic Complex Topology Filter Set

namespace MLC.Quadratic

/-- Differentiability of the fixed-parameter quadratic iterate. -/
lemma differentiable_quadratic_iterate (c : ℂ) (N : ℕ) :
    Differentiable ℂ (fun z => (MLC.quadratic_map c)^[N] z) := by
  induction N with
  | zero =>
      simp only [Function.iterate_zero]
      exact differentiable_id
  | succ n ih =>
      have heq : (fun z => (MLC.quadratic_map c)^[n + 1] z)
          = (fun z => ((MLC.quadratic_map c)^[n] z) ^ 2 + c) := by
        funext z
        rw [Function.iterate_succ_apply']
        simp [MLC.quadratic_map]
      rw [heq]
      exact (ih.pow 2).add (differentiable_const c)

/-- If some iterate of a point has escaped the trapping disk, the point lies in
the basin of infinity. -/
lemma mem_basin_of_iterate_mem_basin (c : ℂ) (N : ℕ) {z : ℂ}
    (h : (MLC.quadratic_map c)^[N] z ∈ basin_of_infinity c) :
    z ∈ basin_of_infinity c := by
  induction N generalizing z with
  | zero => simpa using h
  | succ n ih =>
      have h' : (MLC.quadratic_map c)^[n] (MLC.quadratic_map c z) ∈ basin_of_infinity c := by
        simpa [Function.iterate_succ_apply] using h
      exact basin_of_infinity_preimage_subset c (ih h')

/-- **Stage 1: local holomorphic root branch.** Near any point whose `N`-th
iterate has escaped the trapping disk, there is a holomorphic local branch of the
`2^N`-th root of the near-infinity coordinate pulled back along `f^[N]`, packaged
as `LocalPullbackRootBranchData`. -/
noncomputable def localPullbackRootBranchData_of_iterate_outside
    (c : ℂ) (N : ℕ) (z₀ : ℂ)
    (hz₀ : ‖(MLC.quadratic_map c)^[N] z₀‖ > ‖c‖ + 2) :
    LocalPullbackRootBranchData c N z₀ := by
  classical
  set F : ℂ → ℂ := fun z => MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)
    with hFdef
  set U₀ : Set ℂ := {z : ℂ | ‖c‖ + 2 < ‖(MLC.quadratic_map c)^[N] z‖} with hU₀def
  have hiter_diff : Differentiable ℂ (fun z => (MLC.quadratic_map c)^[N] z) :=
    differentiable_quadratic_iterate c N
  have hU₀open : IsOpen U₀ := by
    have : IsOpen {z : ℂ | ‖c‖ + 2 < ‖(MLC.quadratic_map c)^[N] z‖} :=
      isOpen_lt continuous_const (hiter_diff.continuous.norm)
    simpa [hU₀def] using this
  have hz₀U₀ : z₀ ∈ U₀ := hz₀
  have hlogdiff : DifferentiableOn ℂ (MLC.logSeriesBottcherApprox c)
      {z : ℂ | ‖c‖ + 2 < ‖z‖} :=
    MLC.logSeriesBottcherApprox_differentiableOn_large_radius c (R := ‖c‖ + 2) le_rfl
  have hFdiff : DifferentiableOn ℂ F U₀ := by
    have hcomp : DifferentiableOn ℂ
        (fun z => MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) U₀ := by
      apply hlogdiff.comp hiter_diff.differentiableOn
      intro z hz; exact hz
    simpa [hFdef] using hcomp
  have hFz₀ne : F z₀ ≠ 0 := by
    have : 1 < ‖F z₀‖ :=
      MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hz₀
    intro h; rw [h, norm_zero] at this; linarith
  have hFcontAt : ContinuousAt F z₀ :=
    (hFdiff.differentiableAt (hU₀open.mem_nhds hz₀U₀)).continuousAt
  have hratio_tendsto : Filter.Tendsto (fun z => F z / F z₀) (𝓝 z₀) (𝓝 1) := by
    have : Filter.Tendsto (fun z => F z / F z₀) (𝓝 z₀) (𝓝 (F z₀ / F z₀)) :=
      hFcontAt.tendsto.div_const _
    rwa [div_self hFz₀ne] at this
  have hnear : ∀ᶠ z in 𝓝 z₀, ‖F z / F z₀ - 1‖ < 1 := by
    have := hratio_tendsto (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with z hz
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hUmem : U₀ ∈ 𝓝 z₀ := hU₀open.mem_nhds hz₀U₀
  set U : Set ℂ := U₀ ∩ {z : ℂ | ‖F z / F z₀ - 1‖ < 1} with hUdef
  have hUmem_nhds : U ∈ 𝓝 z₀ := Filter.inter_mem hUmem hnear
  have hz₀U : z₀ ∈ U := by
    refine ⟨hz₀U₀, ?_⟩
    simp only [Set.mem_setOf_eq, div_self hFz₀ne, sub_self, norm_zero]
    norm_num
  set g : ℂ → ℂ :=
    fun z => Complex.exp ((Complex.log (F z / F z₀) + Complex.log (F z₀)) / (2 ^ N)) with hgdef
  have hroot : ∀ z ∈ U, (g z) ^ (2 ^ N) = F z := by
    intro z hz
    have hzU₀ : z ∈ U₀ := hz.1
    have hFzne : F z ≠ 0 := by
      have : 1 < ‖F z‖ :=
        MLC.one_lt_norm_logSeriesBottcherApprox_of_outside_open c hzU₀
      intro h; rw [h, norm_zero] at this; linarith
    have hpow : (g z) ^ (2 ^ N)
        = Complex.exp (Complex.log (F z / F z₀) + Complex.log (F z₀)) := by
      rw [hgdef, ← Complex.exp_nat_mul]
      congr 1
      have hne : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
      push_cast; field_simp
    rw [hpow, Complex.exp_add, Complex.exp_log (div_ne_zero hFzne hFz₀ne),
      Complex.exp_log hFz₀ne, div_mul_cancel₀ _ hFz₀ne]
  have hgdiff : DifferentiableOn ℂ g U := by
    intro z hz
    have hzU₀ : z ∈ U₀ := hz.1
    have hslit : F z / F z₀ ∈ slitPlane :=
      mem_slitPlane_of_norm_sub_one_lt_one hz.2
    have hFat : DifferentiableAt ℂ F z :=
      hFdiff.differentiableAt (hU₀open.mem_nhds hzU₀)
    have hratioAt : DifferentiableAt ℂ (fun z => F z / F z₀) z := hFat.div_const _
    have hlogAt : DifferentiableAt ℂ (fun z => Complex.log (F z / F z₀)) z :=
      hratioAt.clog hslit
    have hLAt : DifferentiableAt ℂ g z := by
      rw [hgdef]
      exact ((hlogAt.add_const _).div_const _).cexp
    exact hLAt.differentiableWithinAt
  exact
    { center_mem_basin :=
        mem_basin_of_iterate_mem_basin c N
          (outside_disk_subset_quadratic_basin c (outside_open_subset_outside_disk c hz₀))
      U := U
      U_mem_nhds := hUmem_nhds
      branch := g
      branch_differentiableOn := hgdiff
      root_eq := fun z hz => by
        have := hroot z hz; simpa [hFdef] using this
      center_value_mem_rootSet := by
        have := hroot z₀ hz₀U
        simpa [pullbackRootSet, hFdef] using this }

end MLC.Quadratic
