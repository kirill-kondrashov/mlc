import Mlc.BasinConnected
import Mlc.Quadratic.Complex.Bottcher.BottcherParamHolo
import Mlc.Quadratic.Complex.ParaPuzzleBasis

namespace MLC.Quadratic

open Set Topology Filter

/-- Fixed-threshold parameter escape levels built from the critical orbit. -/
def ParameterEscapeLevel (n : ℕ) : Set ℂ :=
  {c : ℂ | 2 < ‖orbit c 0 (n + 1)‖}

lemma isOpen_parameterEscapeLevel (n : ℕ) : IsOpen (ParameterEscapeLevel n) := by
  dsimp [ParameterEscapeLevel]
  exact isOpen_lt continuous_const ((continuous_orbit_zero_param (n + 1)).norm)

lemma parameterEscapeLevel_mono {n : ℕ} :
    ParameterEscapeLevel n ⊆ ParameterEscapeLevel (n + 1) := by
  intro c hc
  rcases hc with hc
  dsimp [ParameterEscapeLevel] at hc ⊢
  by_cases hcnorm : ‖c‖ ≤ 2
  · have hstep :
      ‖orbit c 0 (n + 2)‖ = ‖fc c (orbit c 0 (n + 1))‖ := by
        rw [orbit_succ]
    rw [hstep]
    have hgrow := norm_fc_ge_norm_sq_sub_norm_c c (orbit c 0 (n + 1))
    nlinarith
  · have hc_gt : 2 < ‖c‖ := by linarith
    have hnext : ‖orbit c 0 (n + 2)‖ = ‖orbit c c (n + 1)‖ := by
      rw [orbit_param_eq_orbit_zero_succ c (n + 1)]
    have htailNext : ‖orbit c c (n + 1)‖ ≥ ‖c‖ * (‖c‖ - 1) ^ (n + 1) :=
      orbit_param_lower_bound_of_norm_gt_two c hc_gt (n + 1)
    have hgt : 2 < ‖c‖ * (‖c‖ - 1) ^ (n + 1) := by
      have hpowpos : 0 < (‖c‖ - 1) ^ (n + 1) := by
        exact pow_pos (by linarith) _
      have hpowge : 1 ≤ (‖c‖ - 1) ^ (n + 1) := by
        exact one_le_pow₀ (by linarith : 1 ≤ ‖c‖ - 1)
      nlinarith
    rw [hnext]
    linarith

lemma not_mandelbrot_of_mem_parameterEscapeLevel {n : ℕ} {c : ℂ}
    (hc : c ∈ ParameterEscapeLevel n) : c ∉ MandelbrotSet := by
  intro hM
  have hbound0 : boundedOrbit c 0 := hM
  have hball_mem : c ∈ Metric.closedBall (0 : ℂ) 2 := mandelbrotSet_subset_closedBall_two hM
  have hball : ‖c‖ ≤ 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball_mem
  have hcrit : 2 < ‖orbit c 0 (n + 1)‖ := hc
  let z : ℂ := orbit c 0 (n + 1)
  have hz : 2 < ‖z‖ := by simpa [z] using hcrit
  have hgrow : ∀ k : ℕ, ‖orbit c z k‖ ≥ ‖z‖ * (‖z‖ - 1) ^ k := by
    intro k
    induction k with
    | zero => simp [z]
    | succ k ih =>
        rw [orbit_succ]
        have hstep := norm_fc_ge_norm_sq_sub_norm_c c (orbit c z k)
        have hz_le : ‖c‖ ≤ ‖orbit c z k‖ := by
          have hcz : ‖c‖ ≤ ‖z‖ := by linarith
          calc
            ‖c‖ ≤ ‖z‖ := hcz
            _ = ‖z‖ * 1 := by ring
            _ ≤ ‖z‖ * (‖z‖ - 1) ^ k := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact one_le_pow₀ (by linarith : 1 ≤ ‖z‖ - 1)
            _ ≤ ‖orbit c z k‖ := ih
        have horb_ge_z : ‖z‖ ≤ ‖orbit c z k‖ := by
          calc
            ‖z‖ = ‖z‖ * 1 := by ring
            _ ≤ ‖z‖ * (‖z‖ - 1) ^ k := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact one_le_pow₀ (by linarith : 1 ≤ ‖z‖ - 1)
            _ ≤ ‖orbit c z k‖ := ih
        have hmul : ‖orbit c z k‖ * (‖z‖ - 1) ≤ ‖fc c (orbit c z k)‖ := by
          calc
            ‖orbit c z k‖ * (‖z‖ - 1) ≤ ‖orbit c z k‖ * (‖orbit c z k‖ - 1) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              linarith
            _ ≤ ‖orbit c z k‖ ^ 2 - ‖c‖ := by
              nlinarith [hz_le]
            _ ≤ ‖fc c (orbit c z k)‖ := by
              linarith [hstep]
        calc
          ‖fc c (orbit c z k)‖ ≥ ‖orbit c z k‖ * (‖z‖ - 1) := hmul
          _ ≥ (‖z‖ * (‖z‖ - 1) ^ k) * (‖z‖ - 1) := by
            refine mul_le_mul_of_nonneg_right ih ?_
            linarith
          _ = ‖z‖ * (‖z‖ - 1) ^ (k + 1) := by rw [pow_succ]; ring
  have h_tendsto : Tendsto (fun k : ℕ => ‖z‖ * (‖z‖ - 1) ^ k) atTop atTop := by
    refine Filter.Tendsto.const_mul_atTop ?_ ?_
    · linarith
    · exact tendsto_pow_atTop_atTop_of_one_lt (by linarith)
  obtain ⟨B, hB⟩ := hbound0
  rcases (Filter.tendsto_atTop_atTop.mp h_tendsto) (B + 1) with ⟨N, hN⟩
  have htail_eq : orbit c z N = orbit c 0 (N + (n + 1)) := by
    dsimp [z, orbit]
    rw [Function.iterate_add_apply]
    rw [Function.iterate_succ_apply]
  have h_upper : ‖orbit c z N‖ ≤ B := by
    simpa [htail_eq] using hB (N + (n + 1))
  have h_lower : ‖orbit c z N‖ ≥ B + 1 := by
    calc
      ‖orbit c z N‖ ≥ ‖z‖ * (‖z‖ - 1) ^ N := hgrow N
      _ ≥ B + 1 := hN N (le_rfl)
  linarith

theorem compl_mandelbrot_eq_iUnion_parameterEscapeLevel :
    MandelbrotSetᶜ = ⋃ n : ℕ, ParameterEscapeLevel n := by
  ext c
  constructor
  · intro hc
    have h_not_bdd : ¬ boundedOrbit c 0 := hc
    have h_unbounded : ∀ M : ℝ, ∃ n : ℕ, M < ‖orbit c 0 n‖ := by
      intro M
      by_contra hM
      apply h_not_bdd
      refine ⟨M, ?_⟩
      intro n
      by_contra hn
      exact hM ⟨n, lt_of_not_ge hn⟩
    rcases h_unbounded 2 with ⟨m, hm⟩
    cases m with
    | zero =>
        exfalso
        have hzero : ‖orbit c 0 0‖ = 0 := by simp [orbit]
        rw [hzero] at hm
        linarith
    | succ n =>
        refine mem_iUnion.2 ⟨n, ?_⟩
        exact hm
  · intro hc
    rcases mem_iUnion.1 hc with ⟨n, hn⟩
    exact not_mandelbrot_of_mem_parameterEscapeLevel hn

lemma parameterEscapeLevel_zero : ParameterEscapeLevel 0 = {c : ℂ | 2 < ‖c‖} := by
  ext c
  simp [ParameterEscapeLevel, orbit, fc]

lemma exterior_subset_parameterEscapeLevel (n : ℕ) :
    {c : ℂ | 2 < ‖c‖} ⊆ ParameterEscapeLevel n := by
  intro c hc
  have h0 : c ∈ ParameterEscapeLevel 0 := by
    simpa [parameterEscapeLevel_zero] using hc
  induction n with
  | zero => simpa using h0
  | succ n ih => exact parameterEscapeLevel_mono ih

lemma differentiable_orbit_zero_param (n : ℕ) :
    Differentiable ℂ (fun c : ℂ => orbit c 0 n) := by
  simpa [orbit_eq_iter_quadratic_map] using differentiable_iterate_param (0 : ℂ) n

theorem isPreconnected_parameterEscapeLevel (n : ℕ) :
    IsPreconnected (ParameterEscapeLevel n) := by
  set P : ℂ → ℂ := fun c : ℂ => orbit c 0 (n + 1) with hPdef
  have hPdiff : Differentiable ℂ P := by
    simpa [P, hPdef] using differentiable_orbit_zero_param (n + 1)
  have hUopen : IsOpen {c : ℂ | 2 < ‖P c‖} :=
    isOpen_lt continuous_const hPdiff.continuous.norm
  set U : Set ℂ := {c : ℂ | 2 < ‖P c‖} with hUdef
  have hEqU : U = ParameterEscapeLevel n := by
    ext c
    simp [U, P, ParameterEscapeLevel]
  have hEsub : {c : ℂ | 2 < ‖c‖} ⊆ U := by
    intro c hc
    rw [hEqU]
    exact exterior_subset_parameterEscapeLevel n hc
  have hEpre : IsPreconnected {c : ℂ | 2 < ‖c‖} := by
    simpa [R] using exterior_preconnected (0 : ℂ)
  rw [← hEqU]
  intro u v hu hv hUuv hUu hUv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have bounded_side : ∀ w : Set ℂ, IsOpen w → (U ∩ w).Nonempty →
      ({c : ℂ | 2 < ‖c‖} ∩ w = ∅) → frontier (U ∩ w) ⊆ Uᶜ → False := by
    intro w hw hUw hEw hfrontier
    have hBbdd : Bornology.IsBounded (U ∩ w) := by
      apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset
      intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right]
      by_contra hgt
      push_neg at hgt
      have hzE : z ∈ {c : ℂ | 2 < ‖c‖} := hgt
      have : z ∈ ({c : ℂ | 2 < ‖c‖} ∩ w) := ⟨hzE, hz.2⟩
      rw [hEw] at this
      exact this
    have hR0 : R (0 : ℂ) = 2 := by simp [R]
    exact maxmod_absurd (c := 0) hPdiff hBbdd hUw
      (fun x hx => by simpa [U, hR0] using hx.1)
      (fun x hx => by
        have hx' : x ∈ Uᶜ := hfrontier hx
        exact not_lt.1 <| by simpa [U, hR0] using hx')
  by_cases hEv : ({c : ℂ | 2 < ‖c‖} ∩ v).Nonempty
  · by_cases hEu : ({c : ℂ | 2 < ‖c‖} ∩ u).Nonempty
    · have hEuv := hEpre u v hu hv (hEsub.trans hUuv) hEu hEv
      obtain ⟨x, hxE, hxuv⟩ := hEuv
      have hxmem : x ∈ U ∩ (u ∩ v) := ⟨hEsub hxE, hxuv⟩
      rw [hcon] at hxmem
      exact hxmem
    · rw [Set.not_nonempty_iff_eq_empty] at hEu
      have hsep' : U ∩ (v ∩ u) = ∅ := by
        rw [Set.inter_comm v u]
        exact hcon
      exact bounded_side u hu hUu hEu
        (frontier_side_subset_compl hUopen hv hu (by rwa [Set.union_comm] at hUuv) hsep')
  · rw [Set.not_nonempty_iff_eq_empty] at hEv
    exact bounded_side v hv hUv hEv
      (frontier_side_subset_compl hUopen hu hv hUuv hcon)

theorem parameterEscapeLevel_isConnected (n : ℕ) :
    IsConnected (ParameterEscapeLevel n) := by
  have hpre : IsPreconnected (ParameterEscapeLevel n) := isPreconnected_parameterEscapeLevel n
  have hne : (ParameterEscapeLevel n).Nonempty := by
    refine ⟨(3 : ℂ), ?_⟩
    have h : (3 : ℂ) ∈ {c : ℂ | 2 < ‖c‖} := by
      norm_num [Set.mem_setOf_eq]
    exact exterior_subset_parameterEscapeLevel n h
  exact ⟨hne, hpre⟩

theorem mandelbrotSet_compl_isConnected :
    IsConnected (MandelbrotSetᶜ) := by
  rw [compl_mandelbrot_eq_iUnion_parameterEscapeLevel]
  let s : ℕ → Set ℂ := ParameterEscapeLevel
  have hs_conn : ∀ n, IsConnected (s n) := by
    intro n
    simpa [s] using parameterEscapeLevel_isConnected n
  have hs_mono : ∀ m n : ℕ, m ≤ n → s m ⊆ s n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | @step n hle ih => exact ih.trans parameterEscapeLevel_mono
  have hs0_ne : (s 0).Nonempty := by
    simpa [s] using (parameterEscapeLevel_isConnected 0).nonempty
  have hs_link : ∀ n, (s n ∩ s (Order.succ n)).Nonempty := by
    intro n
    rcases hs0_ne with ⟨z, hz⟩
    exact ⟨z, hs_mono 0 n (Nat.zero_le n) hz, hs_mono 0 (n + 1) (Nat.zero_le (n + 1)) hz⟩
  simpa [s] using IsConnected.iUnion_of_chain hs_conn hs_link

end MLC.Quadratic
