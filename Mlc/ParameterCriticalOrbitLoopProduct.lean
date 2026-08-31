import Mlc.ParameterCriticalOrbitPathChain

namespace MLC.Quadratic

open Complex Topology Filter Set Metric

lemma rootsOfUnitySet_mul_mem
    {n : ℕ} {ξ η : ℂ}
    (hξ : ξ ∈ rootsOfUnitySet n) (hη : η ∈ rootsOfUnitySet n) :
    ξ * η ∈ rootsOfUnitySet n := by
  dsimp [rootsOfUnitySet] at hξ hη ⊢
  rw [mul_pow, hξ, hη]
  simp

lemma rootsOfUnitySet_listProd_mem
    {n : ℕ} :
    ∀ L : List ℂ,
      (∀ ξ ∈ L, ξ ∈ rootsOfUnitySet n) →
      L.prod ∈ rootsOfUnitySet n
  | [], _ => by
      simp [one_mem_rootsOfUnitySet n]
  | ξ :: L, h => by
      have hξ : ξ ∈ rootsOfUnitySet n := h ξ (by simp)
      have hL : ∀ η ∈ L, η ∈ rootsOfUnitySet n := by
        intro η hη
        exact h η (by simp [hη])
      simpa using rootsOfUnitySet_mul_mem hξ (rootsOfUnitySet_listProd_mem L hL)

lemma ParameterCriticalOrbitLocalBranchData.overlap_transition_common_level
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL0 : D0.N ≤ L) (hL1 : D1.N ≤ L) :
    ∃ ξ : ℂ, ξ ∈ rootsOfUnitySet (2 ^ L) ∧
      ∀ c ∈ W, D1.G c = ξ * D0.G c := by
  let k0 := L - D0.N
  let k1 := L - D1.N
  have hroot0 : ∀ c ∈ W,
      (D0.G c) ^ (2 ^ L) = logSeriesBottcherApprox c (orbit c 0 (L + 1)) := by
    intro c hc
    simpa [k0, Nat.add_sub_of_le hL0] using D0.root_eq_add k0 c (hW_sub0 hc)
  have hroot1 : ∀ c ∈ W,
      (D1.G c) ^ (2 ^ L) = logSeriesBottcherApprox c (orbit c 0 (L + 1)) := by
    intro c hc
    simpa [k1, Nat.add_sub_of_le hL1] using D1.root_eq_add k1 c (hW_sub1 hc)
  have hA_nonzero : ∀ c ∈ W,
      logSeriesBottcherApprox c (orbit c 0 (L + 1)) ≠ 0 := by
    intro c hc
    simpa [k0, Nat.add_sub_of_le hL0] using D0.nonzero_at_level_add k0 c (hW_sub0 hc)
  let ratio : ℂ → ℂ := fun c => D1.G c / D0.G c
  have hratio_cont : ContinuousOn ratio W := by
    refine (D1.G_diff.continuousOn.mono hW_sub1).div (D0.G_diff.continuousOn.mono hW_sub0) ?_
    intro c hc
    have hroot : (D0.G c) ^ (2 ^ L) = logSeriesBottcherApprox c (orbit c 0 (L + 1)) := hroot0 c hc
    intro hzero
    have hAzero : 0 = logSeriesBottcherApprox c (orbit c 0 (L + 1)) := by simpa [hzero] using hroot
    exact hA_nonzero c hc hAzero.symm
  have hratio_pre : IsPreconnected (ratio '' W) := hW_pre.image ratio hratio_cont
  have hratio_sub : ratio '' W ⊆ rootsOfUnitySet (2 ^ L) := by
    intro ζ hζ
    rcases hζ with ⟨c, hc, rfl⟩
    have hrootset0 : D0.G c ∈ pullbackRootSet (2 ^ L)
        (logSeriesBottcherApprox c (orbit c 0 (L + 1))) := by
      dsimp [pullbackRootSet]
      exact hroot0 c hc
    have hrootset1 : D1.G c ∈ pullbackRootSet (2 ^ L)
        (logSeriesBottcherApprox c (orbit c 0 (L + 1))) := by
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
  rcases pullbackRootSet_torsor_transitive (n := 2 ^ L)
    (pow_ne_zero L (by norm_num : 2 ≠ 0))
    (by dsimp [pullbackRootSet]; exact hroot0 w₀ hw₀)
    (by dsimp [pullbackRootSet]; exact hroot1 w₀ hw₀)
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

structure ParameterLoopTransitionProductData
    (γ : ParameterPath) (hγ : γ.path 0 = γ.path 1) where
  cover : ParameterPathFiniteLocalBranchCover γ
  chain : ParameterPathMeshChain cover
  baseChart : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  baseChart_mem_centers : baseChart ∈ cover.centers
  level : ℕ
  base_le_level : (cover.branchData baseChart).N ≤ level
  left_le_level : ∀ k : Fin (chain.meshSize + 1), (cover.branchData (chain.center k)).N ≤ level
  adjacentMultiplier : Fin chain.meshSize → ℂ
  adjacentMultiplier_mem : ∀ j, adjacentMultiplier j ∈ rootsOfUnitySet (2 ^ level)
  adjacent_eq : ∀ j : Fin chain.meshSize,
    ∀ c ∈ (Classical.choose (chain.overlap_transition_data j)),
      (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).G c =
        adjacentMultiplier j * (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).G c
  closingSet : Set ℂ
  closing_preconnected : IsPreconnected closingSet
  closing_mem : γ.path 0 ∈ closingSet
  closing_subset_base : closingSet ⊆ (cover.branchData baseChart).V
  closing_subset_last : closingSet ⊆ (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).V
  closingMultiplier : ℂ
  closingMultiplier_mem : closingMultiplier ∈ rootsOfUnitySet (2 ^ level)
  closing_eq : ∀ c ∈ closingSet,
    (cover.branchData baseChart).G c =
      closingMultiplier * (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).G c
  product : ℂ
  product_def : product = (List.ofFn adjacentMultiplier).prod * closingMultiplier
  product_mem : product ∈ rootsOfUnitySet (2 ^ level)

noncomputable def ParameterLoopTransitionProductData.of_loop
    (γ : ParameterPath) (hγ : γ.path 0 = γ.path 1) : ParameterLoopTransitionProductData γ hγ := by
  classical
  let cover := ParameterPathFiniteLocalBranchCover.of_path γ
  let chain := cover.toMeshChain
  let baseChart : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} := Classical.choose (cover.cover ⟨0, by simp⟩)
  have hbaseChart_mem : baseChart ∈ cover.centers := by
    exact (Classical.choose_spec (cover.cover ⟨0, by simp⟩)).1
  let level : ℕ := max (cover.branchData baseChart).N
    (Finset.univ.sup (fun k : Fin (chain.meshSize + 1) => (cover.branchData (chain.center k)).N))
  have hbase_level : (cover.branchData baseChart).N ≤ level := by
    exact le_max_left _ _
  have hlevel : ∀ k : Fin (chain.meshSize + 1), (cover.branchData (chain.center k)).N ≤ level := by
    intro k
    exact le_trans
      (Finset.le_sup (s := Finset.univ) (f := fun j : Fin (chain.meshSize + 1) => (cover.branchData (chain.center j)).N)
        (by simp))
      (le_max_right _ _)
  let adjacentTransition : ∀ j : Fin chain.meshSize,
      ∃ ζ ∈ rootsOfUnitySet (2 ^ level),
        ∀ c ∈ (Classical.choose (chain.overlap_transition_data j)),
          (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).G c =
            ζ * (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).G c := by
    intro j
    exact ParameterCriticalOrbitLocalBranchData.overlap_transition_common_level
      (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩))
      (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩))
      (Classical.choose_spec (chain.overlap_transition_data j)).1
      (Classical.choose_spec (chain.overlap_transition_data j)).2.2.1
      (Classical.choose_spec (chain.overlap_transition_data j)).2.2.2
      (Classical.choose_spec (chain.overlap_transition_data j)).2.1
      (hlevel ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)
      (hlevel ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
  let adjacentMultiplier : Fin chain.meshSize → ℂ := fun j =>
    Classical.choose (adjacentTransition j)
  have hadj_mem : ∀ j, adjacentMultiplier j ∈ rootsOfUnitySet (2 ^ level) := by
    intro j
    exact (Classical.choose_spec (adjacentTransition j)).1
  have hadj_eq : ∀ j : Fin chain.meshSize,
      ∀ c ∈ (Classical.choose (chain.overlap_transition_data j)),
        (cover.branchData (chain.center ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)).G c =
          adjacentMultiplier j * (cover.branchData (chain.center ⟨j.1, Nat.lt_trans j.2 (Nat.lt_succ_self _)⟩)).G c := by
    intro j c hc
    exact (Classical.choose_spec (adjacentTransition j)).2 c hc
  have hbase : γ.path 0 ∈ (cover.branchData baseChart).V := by
    exact (Classical.choose_spec (cover.cover ⟨0, by simp⟩)).2
  have hlast : γ.path 1 ∈ (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).V := by
    have hcov := chain.cell_subset ⟨chain.meshSize, Nat.lt_succ_self _⟩
    have hmem : (⟨1, by simp⟩ : {t : ℝ // t ∈ Set.Icc (0:ℝ) 1}) ∈
        {y : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} |
          y.1 ∈ Set.Icc ((chain.meshSize : ℝ) / (chain.meshSize + 1 : ℝ))
            ((((chain.meshSize) + 1 : ℕ) : ℝ) / (chain.meshSize + 1 : ℝ))} := by
      change (1 : ℝ) ∈ Set.Icc ((chain.meshSize : ℝ) / (chain.meshSize + 1 : ℝ))
        ((((chain.meshSize) + 1 : ℕ) : ℝ) / (chain.meshSize + 1 : ℝ))
      have hpos : (0 : ℝ) < (chain.meshSize + 1 : ℝ) := by positivity
      constructor
      · calc
          (chain.meshSize : ℝ) / (chain.meshSize + 1 : ℝ)
              ≤ (chain.meshSize + 1 : ℝ) / (chain.meshSize + 1 : ℝ) := by
                exact div_le_div_of_nonneg_right
                  (by exact_mod_cast Nat.le_succ chain.meshSize) hpos.le
          _ = 1 := div_self (ne_of_gt hpos)
      · have hone : (((chain.meshSize + 1 : ℕ) : ℝ) / (chain.meshSize + 1 : ℝ)) = 1 := by
            norm_num [div_eq_mul_inv, ne_of_gt hpos]
        calc
          (1 : ℝ) = ((chain.meshSize + 1 : ℕ) : ℝ) / (chain.meshSize + 1 : ℝ) := hone.symm
          _ ≤ ((chain.meshSize + 1 : ℕ) : ℝ) / (chain.meshSize + 1 : ℝ) := le_rfl
    exact interior_subset (hcov hmem)
  have hloop0 : γ.path 0 ∈ (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).V := by
    simpa [hγ] using hlast
  let closingBall := overlap_ball_subset_of_mem_interiors
      (cover.branchData baseChart).V_open
      (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).V_open
      hbase hloop0
  let r : ℝ := Classical.choose closingBall
  have hr : 0 < r := (Classical.choose_spec closingBall).1
  have hsub : Metric.ball (γ.path 0) r ⊆
      (cover.branchData baseChart).V ∩
        (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).V :=
    (Classical.choose_spec closingBall).2
  let closingSet : Set ℂ := Metric.ball (γ.path 0) r
  have hclosing_pre : IsPreconnected closingSet := Metric.ball_isPreconnected _ _
  have hclosing_mem : γ.path 0 ∈ closingSet := by simpa [closingSet] using hr
  have hclosing_sub0 : closingSet ⊆ (cover.branchData baseChart).V := by
    intro z hz
    exact (hsub hz).1
  have hclosing_subLast : closingSet ⊆ (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).V := by
    intro z hz
    exact (hsub hz).2
  let closingTransition := ParameterCriticalOrbitLocalBranchData.overlap_transition_common_level
      (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩))
      (cover.branchData baseChart)
      hclosing_pre hclosing_subLast hclosing_sub0 hclosing_mem
      (hlevel ⟨chain.meshSize, Nat.lt_succ_self _⟩)
      hbase_level
  let closingMultiplier : ℂ := Classical.choose closingTransition
  have hclosing_mem_root : closingMultiplier ∈ rootsOfUnitySet (2 ^ level) := by
    exact (Classical.choose_spec closingTransition).1
  have hclosing_eq : ∀ c ∈ closingSet,
      (cover.branchData baseChart).G c =
        closingMultiplier * (cover.branchData (chain.center ⟨chain.meshSize, Nat.lt_succ_self _⟩)).G c := by
    intro c hc
    exact (Classical.choose_spec closingTransition).2 c hc
  let product : ℂ := (List.ofFn adjacentMultiplier).prod * closingMultiplier
  have hproduct_mem : product ∈ rootsOfUnitySet (2 ^ level) := by
    refine rootsOfUnitySet_mul_mem ?_ hclosing_mem_root
    exact rootsOfUnitySet_listProd_mem (List.ofFn adjacentMultiplier) (by
      intro ξ hξ
      rcases List.mem_ofFn.mp hξ with ⟨j, rfl⟩
      exact hadj_mem j)
  refine
    { cover := cover
      chain := chain
      baseChart := baseChart
      baseChart_mem_centers := hbaseChart_mem
      level := level
      base_le_level := hbase_level
      left_le_level := hlevel
      adjacentMultiplier := adjacentMultiplier
      adjacentMultiplier_mem := hadj_mem
      adjacent_eq := hadj_eq
      closingSet := closingSet
      closing_preconnected := hclosing_pre
      closing_mem := hclosing_mem
      closing_subset_base := hclosing_sub0
      closing_subset_last := hclosing_subLast
      closingMultiplier := closingMultiplier
      closingMultiplier_mem := hclosing_mem_root
      closing_eq := hclosing_eq
      product := product
      product_def := rfl
      product_mem := hproduct_mem }

end MLC.Quadratic
