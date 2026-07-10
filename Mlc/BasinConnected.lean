import Mlc.FilledJuliaConnected
import Mlc.Quadratic.Complex.Bottcher.BottcherCore
open MLC MLC.Quadratic Complex Topology Filter Set

namespace MLC.Quadratic

theorem basin_preconnected_of_forall_superlevel_preconnected {c : ℂ}
    (hcrit : ∀ n : ℕ, IsPreconnected {z : ℂ | R c < ‖orbit c z n‖}) :
    IsPreconnected (MLC.Quadratic.basin_of_infinity c) := by
  have hstep : ∀ (k : ℕ) (z : ℂ), R c < ‖orbit c z k‖ → R c < ‖orbit c z (k + 1)‖ := by
    intro k z hk
    have hge : ‖orbit c z (k + 1)‖ ≥ ‖orbit c z k‖ := by
      simpa [orbit_succ] using norm_orbit_ge_of_norm_ge_R c (orbit c z k) 1 hk
    linarith
  have hmono : Monotone (fun n : ℕ => {z : ℂ | R c < ‖orbit c z n‖}) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | @step n hle ih =>
        intro z hz
        exact hstep n z (ih hz)
  have hunion : MLC.Quadratic.basin_of_infinity c
      = ⋃ n, {z : ℂ | R c < ‖orbit c z n‖} := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hz
      have htend : Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
        simpa [MLC.Quadratic.basin_of_infinity, MLC.basin_of_infinity] using hz
      have htend' : Tendsto (fun k => ‖orbit c z k‖) atTop atTop := by
        simpa [orbit_eq_iter_quadratic_map c z] using htend
      obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 ((Filter.tendsto_atTop.1 htend') (R c + 1)))
      exact ⟨N, by have := hN N le_rfl; linarith⟩
    · rintro ⟨n, hn⟩
      have hgt : ‖orbit c z n‖ > R c := hn
      have htend' : Tendsto (fun k => ‖orbit c z k‖) atTop atTop := by
        rw [Filter.tendsto_atTop]; intro M
        obtain ⟨Nn, hNn⟩ := (MLC.Quadratic.escape_lemma (c := c) (z := z) n hgt) M
        rw [Filter.eventually_atTop]; exact ⟨Nn, fun m hm => le_of_lt (hNn m hm)⟩
      have htend : Tendsto (fun n => ‖(MLC.quadratic_map c)^[n] z‖) atTop atTop := by
        simpa [orbit_eq_iter_quadratic_map c z] using htend'
      simpa [MLC.Quadratic.basin_of_infinity, MLC.basin_of_infinity] using htend
  have hInterNe : (⋂ n, {z : ℂ | R c < ‖orbit c z n‖}).Nonempty := by
    refine ⟨((R c + 1 : ℝ) : ℂ), ?_⟩
    rw [Set.mem_iInter]
    intro n
    have hRpos : (0 : ℝ) < R c := R_pos c
    have hbase : ((R c + 1 : ℝ) : ℂ) ∈ {z : ℂ | R c < ‖orbit c z 0‖} := by
      simp only [Set.mem_setOf_eq, orbit_zero, Complex.norm_real]
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
    exact hmono (Nat.zero_le n) hbase
  rw [hunion]
  exact isPreconnected_iUnion hInterNe hcrit

lemma differentiable_orbit (c : ℂ) (n : ℕ) :
    Differentiable ℂ (fun z => orbit c z n) := by
  induction n with
  | zero => simp only [orbit_zero]; exact differentiable_id
  | succ n ih =>
      have heq : (fun z => orbit c z (n + 1)) = (fun z => (orbit c z n) ^ 2 + c) := by
        funext z; rw [orbit_succ]; rfl
      rw [heq]
      exact (ih.pow 2).add (differentiable_const c)

lemma exterior_subset_superlevel (c : ℂ) (n : ℕ) :
    {z : ℂ | R c < ‖z‖} ⊆ {z : ℂ | R c < ‖orbit c z n‖} := by
  intro z hz
  exact lt_of_lt_of_le hz (norm_orbit_ge_of_norm_ge_R c z n hz)

lemma exterior_preconnected (c : ℂ) : IsPreconnected {z : ℂ | R c < ‖z‖} := by
  have hcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)) := by
    fun_prop
  have hpre : IsPreconnected ((Set.Ioi (R c)) ×ˢ (Set.univ : Set ℝ)) :=
    isPreconnected_Ioi.prod isPreconnected_univ
  have himg := hpre.image _ hcont.continuousOn
  have hset : (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I))
        '' ((Set.Ioi (R c)) ×ˢ (Set.univ : Set ℝ)) = {z : ℂ | R c < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      simp only [Set.mem_setOf_eq, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
        mul_one]
      rw [Real.norm_of_nonneg (le_of_lt (lt_trans (R_pos c) ht))]
      exact ht
    · intro hz
      refine ⟨(‖z‖, Complex.arg z), ⟨hz, Set.mem_univ _⟩, ?_⟩
      simpa using Complex.abs_mul_exp_arg_mul_I z
  rwa [hset] at himg

/-- Max-modulus contradiction: an entire `P` cannot exceed `R c` throughout a bounded
open set while staying `≤ R c` on its frontier. -/
lemma maxmod_absurd {c : ℂ} {P : ℂ → ℂ} (hPdiff : Differentiable ℂ P)
    {B : Set ℂ} (hBbdd : Bornology.IsBounded B) (hBne : B.Nonempty)
    (hin : ∀ x ∈ B, R c < ‖P x‖) (hfr : ∀ x ∈ frontier B, ‖P x‖ ≤ R c) : False := by
  obtain ⟨z0, hz0f, hz0max⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm hBbdd hBne hPdiff.diffContOnCl
  obtain ⟨b, hbB⟩ := hBne
  have h1 : R c < ‖P b‖ := hin b hbB
  have h2 : ‖P z0‖ ≤ R c := hfr z0 hz0f
  have h3 : ‖P b‖ ≤ ‖P z0‖ := hz0max (subset_closure hbB)
  linarith

/-- Frontier of the `b`-side of a separation lies outside `U`. -/
lemma frontier_side_subset_compl {U u v : Set ℂ} (hUopen : IsOpen U)
    (hu : IsOpen u) (hv : IsOpen v) (hUuv : U ⊆ u ∪ v) (hsep : U ∩ (u ∩ v) = ∅) :
    frontier (U ∩ v) ⊆ Uᶜ := by
  intro x hx
  rw [frontier, Set.mem_diff] at hx
  obtain ⟨hxcl, hxnint⟩ := hx
  intro hxU
  rcases hUuv hxU with hxu | hxv
  · -- x ∈ u : the open nbhd u ∩ U is disjoint from U ∩ v
    have hoa : IsOpen (u ∩ U) := hu.inter hUopen
    have hmem : x ∈ u ∩ U := ⟨hxu, hxU⟩
    have hdisj : (u ∩ U) ∩ (U ∩ v) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have hy2 : y ∈ U ∩ (u ∩ v) := ⟨hy.1.2, hy.1.1, hy.2.2⟩
      rw [hsep] at hy2
      exact hy2
    have hxnotcl : x ∉ closure (U ∩ v) := by
      rw [mem_closure_iff]; push_neg
      exact ⟨u ∩ U, hoa, hmem, hdisj⟩
    exact hxnotcl hxcl
  · -- x ∈ v : then x ∈ interior (U ∩ v), contradicting frontier
    have : x ∈ U ∩ v := ⟨hxU, hxv⟩
    have hint : x ∈ interior (U ∩ v) := by
      rw [(hUopen.inter hv).interior_eq]; exact this
    exact hxnint hint

theorem isPreconnected_orbit_superlevel (c : ℂ) (n : ℕ) :
    IsPreconnected {z : ℂ | R c < ‖orbit c z n‖} := by
  set P : ℂ → ℂ := fun z => orbit c z n with hPdef
  have hPdiff : Differentiable ℂ P := differentiable_orbit c n
  have hUopen : IsOpen {z : ℂ | R c < ‖P z‖} :=
    isOpen_lt continuous_const hPdiff.continuous.norm
  set U : Set ℂ := {z : ℂ | R c < ‖P z‖} with hUdef
  have hEsub : {z : ℂ | R c < ‖z‖} ⊆ U := exterior_subset_superlevel c n
  have hEpre : IsPreconnected {z : ℂ | R c < ‖z‖} := exterior_preconnected c
  intro u v hu hv hUuv hUu hUv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  -- The bounded side leads to a max-modulus contradiction.
  -- Helper: given the side set `w` that the exterior avoids, build the contradiction.
  have bounded_side : ∀ w : Set ℂ, IsOpen w → (U ∩ w).Nonempty →
      ({z : ℂ | R c < ‖z‖} ∩ w = ∅) → frontier (U ∩ w) ⊆ Uᶜ → False := by
    intro w hw hUw hEw hfrontier
    have hBbdd : Bornology.IsBounded (U ∩ w) := by
      apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R c)).subset
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right]
      by_contra hgt
      push_neg at hgt
      have hzE : z ∈ {z : ℂ | R c < ‖z‖} := hgt
      have : z ∈ ({z : ℂ | R c < ‖z‖} ∩ w) := ⟨hzE, hz.2⟩
      rw [hEw] at this; exact this
    exact maxmod_absurd hPdiff hBbdd hUw
      (fun x hx => hx.1) (fun x hx => not_lt.1 (hfrontier hx))
  by_cases hEv : ({z : ℂ | R c < ‖z‖} ∩ v).Nonempty
  · by_cases hEu : ({z : ℂ | R c < ‖z‖} ∩ u).Nonempty
    · have hEuv := hEpre u v hu hv (hEsub.trans hUuv) hEu hEv
      obtain ⟨x, hxE, hxuv⟩ := hEuv
      have hxmem : x ∈ U ∩ (u ∩ v) := ⟨hEsub hxE, hxuv⟩
      rw [hcon] at hxmem; exact hxmem
    · -- E ∩ u = ∅ : bounded side is U ∩ u
      rw [Set.not_nonempty_iff_eq_empty] at hEu
      have hsep' : U ∩ (v ∩ u) = ∅ := by rw [Set.inter_comm v u]; exact hcon
      exact bounded_side u hu hUu hEu
        (frontier_side_subset_compl hUopen hv hu (by rwa [Set.union_comm] at hUuv) hsep')
  · -- E ∩ v = ∅ : bounded side is U ∩ v
    rw [Set.not_nonempty_iff_eq_empty] at hEv
    exact bounded_side v hv hUv hEv
      (frontier_side_subset_compl hUopen hu hv hUuv hcon)

/-- **The basin of infinity is preconnected** (for every parameter `c`). -/
theorem basin_of_infinity_isPreconnected (c : ℂ) :
    IsPreconnected (MLC.Quadratic.basin_of_infinity c) :=
  basin_preconnected_of_forall_superlevel_preconnected
    (fun n => isPreconnected_orbit_superlevel c n)

end MLC.Quadratic
