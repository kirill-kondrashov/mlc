import Mlc.ParameterEscapeExhaustion
import Mlc.BottcherLocalRootBranch
import Mlc.BottcherFiniteLevelCoherence
import Mlc.BottcherArbitraryFiniteLevelLift
import Mlc.Quadratic.Complex.Bottcher.BottcherJointDeriv

namespace MLC.Quadratic

open Complex Topology Filter Set Metric

lemma mem_mandelbrot_of_mem_K (c : ℂ) (hc : c ∈ K c) : c ∈ MandelbrotSet := by
  rcases hc with ⟨B, hB⟩
  refine ⟨max (B : ℝ) ‖c‖, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨m, rfl⟩
    have hshift : orbit c 0 (m + 1) = orbit c c m := by
      simpa using (orbit_param_eq_orbit_zero_succ c m).symm
    rw [hshift]
    exact le_trans (hB m) (le_max_left (B : ℝ) ‖c‖)

lemma mem_basin_criticalValue_of_not_mandelbrot (c : ℂ) (hc : c ∉ MandelbrotSet) :
    c ∈ basin_of_infinity c := by
  have hnotK : c ∉ K c := by
    intro hcK
    exact hc (mem_mandelbrot_of_mem_K c hcK)
  have hcompl : c ∈ (K c)ᶜ := by simpa [Set.mem_compl_iff] using hnotK
  simpa [basin_eq_compl_K c] using hcompl

lemma differentiable_parameterCriticalOrbitGraph (N : ℕ) :
    Differentiable ℂ (fun c : ℂ => (c, orbit c 0 (N + 1))) := by
  exact differentiable_id.prodMk (differentiable_orbit_zero_param (N + 1))

/-- Concrete local data for a parameter-space pullback branch of the escaped
critical orbit. -/
structure ParameterCriticalOrbitLocalBranchData (c₀ : ℂ) where
  N : ℕ
  V : Set ℂ
  V_mem : V ∈ 𝓝 c₀
  V_open : IsOpen V
  G : ℂ → ℂ
  G_diff : DifferentiableOn ℂ G V
  outside : ∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2
  root_eq : ∀ c ∈ V,
    (G c) ^ (2 ^ N) =
      logSeriesBottcherApprox c (orbit c 0 (N + 1))

/-- A local parameter-space `2^N`-th root branch for the escaped critical orbit. -/
theorem exists_parameterCriticalOrbitLocalRootBranch
    (c₀ : ℂ) (hc₀ : c₀ ∉ MandelbrotSet) :
    ∃ N : ℕ, ∃ V : Set ℂ, V ∈ 𝓝 c₀ ∧ IsOpen V ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G V ∧
        (∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2) ∧
        ∀ c ∈ V,
          (G c) ^ (2 ^ N) =
            logSeriesBottcherApprox c (orbit c 0 (N + 1)) := by
  have hbasin : c₀ ∈ basin_of_infinity c₀ :=
    mem_basin_criticalValue_of_not_mandelbrot c₀ hc₀
  rcases exists_iterate_mem_outside_open_of_mem_basin c₀ c₀ hbasin with ⟨N, hN⟩
  have hz0' : ‖orbit c₀ c₀ N‖ > ‖c₀‖ + 2 := by
    simpa [orbit_eq_iter_quadratic_map] using hN
  have hz0 : ‖orbit c₀ 0 (N + 1)‖ > ‖c₀‖ + 2 := by
    simpa [orbit_param_eq_orbit_zero_succ] using hz0'
  set z₀ : ℂ := orbit c₀ 0 (N + 1) with hz₀def
  have hgap : 0 < ‖z₀‖ - (‖c₀‖ + 2) := by
    dsimp [z₀]
    linarith
  set a : ℝ := (‖z₀‖ - (‖c₀‖ + 2)) / 4 with hadef
  have ha : 0 < a := by
    rw [hadef]
    linarith
  have hzjoint : ‖c₀‖ + 3 * a + 2 < ‖z₀‖ := by
    rw [hadef]
    linarith
  set Graph : ℂ → ℂ × ℂ := fun c => (c, orbit c 0 (N + 1)) with hGraph
  have hGraphDiff : Differentiable ℂ Graph := by
    simpa [Graph, hGraph] using differentiable_parameterCriticalOrbitGraph N
  have hGraphCont : Continuous Graph := hGraphDiff.continuous
  have hGraphMem : Graph c₀ ∈ ball c₀ a ×ˢ ball z₀ a := by
    rw [hGraph, hz₀def, Set.mem_prod, mem_ball, mem_ball, dist_self, dist_self]
    exact ⟨ha, ha⟩
  have hpre : Graph ⁻¹' (ball c₀ a ×ˢ ball z₀ a) ∈ 𝓝 c₀ :=
    hGraphCont.continuousAt.preimage_mem_nhds ((isOpen_ball.prod isOpen_ball).mem_nhds hGraphMem)
  set F : ℂ → ℂ := fun c => logSeriesBottcherApprox c (orbit c 0 (N + 1)) with hF
  have hGraphOpen : IsOpen (ball c₀ a ×ˢ ball z₀ a) := isOpen_ball.prod isOpen_ball
  have hFdiff_raw : DifferentiableOn ℂ F (Graph ⁻¹' (ball c₀ a ×ˢ ball z₀ a)) := by
    intro c hc
    have hjoint : DifferentiableAt ℂ (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) (Graph c) :=
      logSeriesBottcherApprox_differentiableAt_joint ha hzjoint hc
    have hgraphAt : DifferentiableAt ℂ Graph c := hGraphDiff.differentiableAt
    exact (hjoint.comp c hgraphAt).differentiableWithinAt
  have hFz0ne : F c₀ ≠ 0 := by
    have : 1 < ‖F c₀‖ := by
      simpa [F, hF, hz₀def] using one_lt_norm_logSeriesBottcherApprox_of_outside_open c₀ (by linarith : ‖c₀‖ + 2 < ‖z₀‖)
    intro hzero
    rw [hzero, norm_zero] at this
    linarith
  have hFcontAt : ContinuousAt F c₀ :=
    (hFdiff_raw.differentiableAt hpre).continuousAt
  have hratio_tendsto : Filter.Tendsto (fun c => F c / F c₀) (𝓝 c₀) (𝓝 1) := by
    have : Filter.Tendsto (fun c => F c / F c₀) (𝓝 c₀) (𝓝 (F c₀ / F c₀)) :=
      hFcontAt.tendsto.div_const _
    rwa [div_self hFz0ne] at this
  have hnear : {c : ℂ | ‖F c / F c₀ - 1‖ < 1} ∈ 𝓝 c₀ := by
    have := hratio_tendsto (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1))
    simpa [Metric.ball, dist_eq_norm] using this
  set Vraw : Set ℂ := Graph ⁻¹' (ball c₀ a ×ˢ ball z₀ a) ∩ {c : ℂ | ‖F c / F c₀ - 1‖ < 1} with hVraw
  have hVraw_mem : Vraw ∈ 𝓝 c₀ := Filter.inter_mem hpre hnear
  rcases Metric.mem_nhds_iff.mp hVraw_mem with ⟨ε, hεpos, hεsub⟩
  set V : Set ℂ := ball c₀ ε with hV
  have hVmem : V ∈ 𝓝 c₀ := by simpa [V, hV] using Metric.ball_mem_nhds c₀ hεpos
  have hVopen : IsOpen V := by simpa [V, hV] using Metric.isOpen_ball
  have hVsub : V ⊆ Vraw := by simpa [V, hV] using hεsub
  set G : ℂ → ℂ :=
    fun c => Complex.exp ((Complex.log (F c / F c₀) + Complex.log (F c₀)) / (2 ^ N)) with hG
  refine ⟨N, V, hVmem, hVopen, G, ?_, ?_, ?_⟩
  · intro c hcV
    have hcRaw : c ∈ Vraw := hVsub hcV
    have hcGraph : c ∈ Graph ⁻¹' (ball c₀ a ×ˢ ball z₀ a) := hcRaw.1
    have hslit : F c / F c₀ ∈ slitPlane := mem_slitPlane_of_norm_sub_one_lt_one hcRaw.2
    have hcPre : c ∈ Graph ⁻¹' (ball c₀ a ×ˢ ball z₀ a) := (hVsub hcV).1
    have hFat : DifferentiableAt ℂ F c := by
      have hjoint : DifferentiableAt ℂ (fun p : ℂ × ℂ => logSeriesBottcherApprox p.1 p.2) (Graph c) :=
        logSeriesBottcherApprox_differentiableAt_joint ha hzjoint hcPre
      have hgraphAt : DifferentiableAt ℂ Graph c := hGraphDiff.differentiableAt
      simpa [F, hF, Graph, hGraph] using hjoint.comp c hgraphAt
    have hratioAt : DifferentiableAt ℂ (fun c => F c / F c₀) c := hFat.div_const _
    have hlogAt : DifferentiableAt ℂ (fun c => Complex.log (F c / F c₀)) c := hratioAt.clog hslit
    have hGat : DifferentiableAt ℂ G c := by
      rw [hG]
      exact ((hlogAt.add_const _).div_const _).cexp
    exact hGat.differentiableWithinAt
  · intro c hcV
    have hcRaw : c ∈ Vraw := hVsub hcV
    have hcGraph : Graph c ∈ ball c₀ a ×ˢ ball z₀ a := hcRaw.1
    rcases hcGraph with ⟨hc1, hc2⟩
    rw [mem_ball, dist_eq_norm] at hc1 hc2
    calc
      ‖c‖ + 2 < (‖c₀‖ + a) + 2 := by
        have hcnorm : ‖c‖ < ‖c₀‖ + a := by
          calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
            _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
            _ < a + ‖c₀‖ := by linarith
            _ = ‖c₀‖ + a := by ring
        linarith
      _ < ‖z₀‖ - a := by linarith [hzjoint]
      _ ≤ ‖orbit c 0 (N + 1)‖ := by
        have hdist : ‖orbit c 0 (N + 1) - z₀‖ < a := by
          simpa [Graph, hGraph, z₀, hz₀def] using hc2
        have hlower : ‖z₀‖ - a < ‖orbit c 0 (N + 1)‖ := by
          have htmp := norm_sub_norm_le z₀ (orbit c 0 (N + 1))
          rw [norm_sub_rev] at htmp
          linarith
        exact le_of_lt hlower
  · intro c hcV
    have houtside : ‖c‖ + 2 < ‖orbit c 0 (N + 1)‖ := by
      have hcRaw : c ∈ Vraw := hVsub hcV
      have hcGraph : Graph c ∈ ball c₀ a ×ˢ ball z₀ a := hcRaw.1
      rcases hcGraph with ⟨hc1, hc2⟩
      rw [mem_ball, dist_eq_norm] at hc1 hc2
      calc
        ‖c‖ + 2 < (‖c₀‖ + a) + 2 := by
          have hcnorm : ‖c‖ < ‖c₀‖ + a := by
            calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
              _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
              _ < a + ‖c₀‖ := by linarith
              _ = ‖c₀‖ + a := by ring
          linarith
        _ < ‖z₀‖ - a := by linarith [hzjoint]
        _ ≤ ‖orbit c 0 (N + 1)‖ := by
          have hdist : ‖orbit c 0 (N + 1) - z₀‖ < a := by
            simpa [Graph, hGraph, z₀, hz₀def] using hc2
          have hlower : ‖z₀‖ - a < ‖orbit c 0 (N + 1)‖ := by
            have htmp := norm_sub_norm_le z₀ (orbit c 0 (N + 1))
            rw [norm_sub_rev] at htmp
            linarith
          exact le_of_lt hlower
    have hFcne : F c ≠ 0 := by
      have : 1 < ‖F c‖ := by
        simpa [F, hF] using one_lt_norm_logSeriesBottcherApprox_of_outside_open c houtside
      intro hzero
      rw [hzero, norm_zero] at this
      linarith
    have hpow : (G c) ^ (2 ^ N) = Complex.exp (Complex.log (F c / F c₀) + Complex.log (F c₀)) := by
      rw [hG, ← Complex.exp_nat_mul]
      congr 1
      have hne : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
      push_cast
      field_simp
    rw [hpow, Complex.exp_add, Complex.exp_log (div_ne_zero hFcne hFz0ne),
      Complex.exp_log hFz0ne, div_mul_cancel₀ _ hFz0ne]

/-- Package the existential Prompt 104 local branch into reusable concrete data. -/
theorem exists_parameterCriticalOrbitLocalBranchData
    (c₀ : ℂ) (hc₀ : c₀ ∉ MandelbrotSet) :
    ∃ D : ParameterCriticalOrbitLocalBranchData c₀, True := by
  rcases exists_parameterCriticalOrbitLocalRootBranch c₀ hc₀ with
    ⟨N, V, hVmem, hVopen, G, hGdiff, houtside, hroot⟩
  refine ⟨{
    N := N
    V := V
    V_mem := hVmem
    V_open := hVopen
    G := G
    G_diff := hGdiff
    outside := houtside
    root_eq := hroot
  }, trivial⟩

/-- The packaged local parameter branch stays coherent at every common future
escape level on the same neighborhood. -/
theorem ParameterCriticalOrbitLocalBranchData.root_eq_add
    {c₀ : ℂ} (D : ParameterCriticalOrbitLocalBranchData c₀) (k : ℕ) :
    ∀ c ∈ D.V,
      (D.G c) ^ (2 ^ (D.N + k)) =
        logSeriesBottcherApprox c (orbit c 0 (D.N + k + 1)) := by
  induction k with
  | zero =>
      intro c hc
      simpa using D.root_eq c hc
  | succ k ih =>
      intro c hc
      have hprev := ih c hc
      have hout : ‖orbit c 0 (D.N + k + 1)‖ > ‖c‖ + 2 := by
        simpa [orbit_eq_iter_quadratic_map, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          outside_iterate_add_of_outside c 0 (D.N + 1) k (D.outside c hc)
      have hsucc := logSeriesBottcherApprox_iterate_succ_eq_sq c hout
      calc
        (D.G c) ^ (2 ^ (D.N + (k + 1))) = ((D.G c) ^ (2 ^ (D.N + k))) ^ 2 := by
          have hexp : 2 ^ (D.N + (k + 1)) = (2 ^ (D.N + k)) * 2 := by
            calc
              2 ^ (D.N + (k + 1)) = 2 ^ ((D.N + k) + 1) := by ac_rfl
              _ = 2 ^ (D.N + k) * 2 ^ 1 := by rw [pow_add]
              _ = (2 ^ (D.N + k)) * 2 := by norm_num
          rw [hexp, pow_mul]
        _ = (logSeriesBottcherApprox c (orbit c 0 (D.N + k + 1))) ^ 2 := by
          rw [hprev]
        _ = logSeriesBottcherApprox c (orbit c 0 (D.N + (k + 1) + 1)) := by
          simpa [orbit_eq_iter_quadratic_map, MLC.Quadratic.orbit, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsucc.symm

lemma ParameterCriticalOrbitLocalBranchData.nonzero_at_level_add
    {c₀ : ℂ} (D : ParameterCriticalOrbitLocalBranchData c₀) (k : ℕ) :
    ∀ c ∈ D.V,
      logSeriesBottcherApprox c (orbit c 0 (D.N + k + 1)) ≠ 0 := by
  intro c hc
  have hout : ‖orbit c 0 (D.N + k + 1)‖ > ‖c‖ + 2 := by
    simpa [orbit_eq_iter_quadratic_map, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      outside_iterate_add_of_outside c 0 (D.N + 1) k (D.outside c hc)
  have hnorm : 1 < ‖logSeriesBottcherApprox c (orbit c 0 (D.N + k + 1))‖ := by
    simpa using one_lt_norm_logSeriesBottcherApprox_of_outside_open c hout
  intro hzero
  rw [hzero, norm_zero] at hnorm
  linarith

/-- On a preconnected overlap, two parameter-local charts differ by a constant
`2^L`-th root-of-unity multiplier after lifting both branches to the common
level `L = max D0.N D1.N`. -/
theorem ParameterCriticalOrbitLocalBranchData.overlap_transition
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W) :
    ∃ ξ : ℂ, ξ ∈ rootsOfUnitySet (2 ^ max D0.N D1.N) ∧
      ∀ c ∈ W, D1.G c = ξ * D0.G c := by
  let L := max D0.N D1.N
  let k0 := L - D0.N
  let k1 := L - D1.N
  have hL0 : D0.N + k0 = L := Nat.add_sub_of_le (le_max_left _ _)
  have hL1 : D1.N + k1 = L := Nat.add_sub_of_le (le_max_right _ _)
  let A : ℂ → ℂ := fun c => logSeriesBottcherApprox c (orbit c 0 (L + 1))
  have hroot0 : ∀ c ∈ W, (D0.G c) ^ (2 ^ L) = A c := by
    intro c hc
    simpa [A, hL0] using D0.root_eq_add k0 c (hW_sub0 hc)
  have hroot1 : ∀ c ∈ W, (D1.G c) ^ (2 ^ L) = A c := by
    intro c hc
    simpa [A, hL1] using D1.root_eq_add k1 c (hW_sub1 hc)
  have hA_nonzero : ∀ c ∈ W, A c ≠ 0 := by
    intro c hc
    simpa [A, hL0] using D0.nonzero_at_level_add k0 c (hW_sub0 hc)
  let ratio : ℂ → ℂ := fun c => D1.G c / D0.G c
  have hratio_cont : ContinuousOn ratio W := by
    refine (D1.G_diff.continuousOn.mono hW_sub1).div (D0.G_diff.continuousOn.mono hW_sub0) ?_
    intro c hc
    have hroot : (D0.G c) ^ (2 ^ L) = A c := hroot0 c hc
    intro hzero
    have hAzero : 0 = A c := by simpa [hzero] using hroot
    exact hA_nonzero c hc hAzero.symm
  have hratio_pre : IsPreconnected (ratio '' W) := hW_pre.image ratio hratio_cont
  have hratio_sub : ratio '' W ⊆ rootsOfUnitySet (2 ^ L) := by
    intro ζ hζ
    rcases hζ with ⟨c, hc, rfl⟩
    have hrootset0 : D0.G c ∈ pullbackRootSet (2 ^ L) (A c) := by
      dsimp [pullbackRootSet]
      exact hroot0 c hc
    have hrootset1 : D1.G c ∈ pullbackRootSet (2 ^ L) (A c) := by
      dsimp [pullbackRootSet]
      exact hroot1 c hc
    rcases pullbackRootSet_torsor_transitive (n := 2 ^ L)
      (pow_ne_zero L (by norm_num : 2 ≠ 0))
      hrootset0 hrootset1 (hA_nonzero c hc) with ⟨η, hη, hmul⟩
    have hG0_ne : D0.G c ≠ 0 := by
      intro hzero
      have hpow0 : (D0.G c) ^ (2 ^ L) = 0 := by simp [hzero]
      rw [hroot0 c hc] at hpow0
      exact hA_nonzero c hc hpow0
    have hratio_eq : ratio c = η := by
      dsimp [ratio]
      rw [hmul]
      field_simp [hG0_ne]
    rw [hratio_eq]
    exact hη
  have hsubsingleton : (ratio '' W).Subsingleton := by
    exact (Set.Countable.isTotallyDisconnected
      (rootsOfUnitySet_countable (2 ^ L) (pow_ne_zero L (by norm_num : 2 ≠ 0))))
      _ hratio_sub hratio_pre
  have hrootset0_w0 : D0.G w₀ ∈ pullbackRootSet (2 ^ L) (A w₀) := by
    dsimp [pullbackRootSet]
    exact hroot0 w₀ hw₀
  have hrootset1_w0 : D1.G w₀ ∈ pullbackRootSet (2 ^ L) (A w₀) := by
    dsimp [pullbackRootSet]
    exact hroot1 w₀ hw₀
  rcases pullbackRootSet_torsor_transitive (n := 2 ^ L)
    (pow_ne_zero L (by norm_num : 2 ≠ 0))
    hrootset0_w0 hrootset1_w0
    (hA_nonzero w₀ hw₀) with ⟨ξ, hξ, hξmul⟩
  refine ⟨ξ, hξ, ?_⟩
  intro c hc
  have hw0_img : ratio w₀ ∈ ratio '' W := ⟨w₀, hw₀, rfl⟩
  have hc_img : ratio c ∈ ratio '' W := ⟨c, hc, rfl⟩
  have hconst : ratio c = ratio w₀ := hsubsingleton hc_img hw0_img
  have hG0w_ne : D0.G w₀ ≠ 0 := by
    intro hzero
    have hpow0 : (D0.G w₀) ^ (2 ^ L) = 0 := by simp [hzero]
    rw [hroot0 w₀ hw₀] at hpow0
    exact hA_nonzero w₀ hw₀ hpow0
  have hratio_w0 : ratio w₀ = ξ := by
    dsimp [ratio]
    rw [hξmul]
    field_simp [hG0w_ne]
  have hratio_c : ratio c = ξ := by rw [hconst, hratio_w0]
  have hG0_ne : D0.G c ≠ 0 := by
    intro hzero
    have hpow0 : (D0.G c) ^ (2 ^ L) = 0 := by simp [hzero]
    rw [hroot0 c hc] at hpow0
    exact hA_nonzero c hc hpow0
  exact (div_eq_iff hG0_ne).mp hratio_c
theorem exists_parameterCriticalOrbitLocalRootBranch_coherentSucc
    (c₀ : ℂ) (hc₀ : c₀ ∉ MandelbrotSet) :
    ∃ N : ℕ, ∃ V : Set ℂ, ∃ G : ℂ → ℂ,
      V ∈ 𝓝 c₀ ∧ IsOpen V ∧ DifferentiableOn ℂ G V ∧
      (∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2) ∧
      (∀ c ∈ V,
        (G c) ^ (2 ^ N) =
          logSeriesBottcherApprox c (orbit c 0 (N + 1))) ∧
      (∀ c ∈ V,
        (G c) ^ (2 ^ (N + 1)) =
          logSeriesBottcherApprox c (orbit c 0 (N + 2))) := by
  rcases exists_parameterCriticalOrbitLocalRootBranch c₀ hc₀ with ⟨N, V, hVnhds, hVopen, G, hGdiff, houtside, hroot⟩
  refine ⟨N, V, G, hVnhds, hVopen, hGdiff, houtside, hroot, ?_⟩
  · intro c hcV
    have hrootN := hroot c hcV
    have hsucc := logSeriesBottcherApprox_iterate_succ_eq_sq c (houtside c hcV)
    calc
      (G c) ^ (2 ^ (N + 1)) = ((G c) ^ (2 ^ N)) ^ 2 := by
        rw [show 2 ^ (N + 1) = (2 ^ N) * 2 by simp [pow_succ, Nat.mul_comm], pow_mul]
      _ = (logSeriesBottcherApprox c (orbit c 0 (N + 1))) ^ 2 := by rw [hrootN]
      _ = logSeriesBottcherApprox c (orbit c 0 (N + 2)) := by
        simpa [orbit_eq_iter_quadratic_map, MLC.Quadratic.orbit] using hsucc.symm

end MLC.Quadratic
