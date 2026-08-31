import Mlc.ParameterCriticalOrbitLoopProduct

namespace MLC.Quadratic

open Complex Topology Filter Set Metric

noncomputable def ParameterCriticalOrbitLocalBranchData.canonicalTransition
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (_hW_pre : IsPreconnected W)
    (_hW_sub0 : W ⊆ D0.V)
    (_hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (_hw₀ : w₀ ∈ W)
    {L : ℕ} (_hL0 : D0.N ≤ L) (_hL1 : D1.N ≤ L) : ℂ :=
  D1.G w₀ / D0.G w₀

private lemma branch_nonzero_at_common_level
    {c₀ : ℂ}
    (D : ParameterCriticalOrbitLocalBranchData c₀)
    {W : Set ℂ}
    (hW_sub : W ⊆ D.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL : D.N ≤ L) :
    D.G w₀ ≠ 0 := by
  let k := L - D.N
  have hlevel : D.N + k = L := Nat.add_sub_of_le hL
  have hroot :
      (D.G w₀) ^ (2 ^ L) =
        logSeriesBottcherApprox w₀ (orbit w₀ 0 (L + 1)) := by
    simpa [k, hlevel] using D.root_eq_add k w₀ (hW_sub hw₀)
  intro hzero
  have hpow0 : (D.G w₀) ^ (2 ^ L) = 0 := by simp [hzero]
  rw [hroot] at hpow0
  have hnonzero :=
    D.nonzero_at_level_add k w₀ (hW_sub hw₀)
  have hpow0' :
      logSeriesBottcherApprox w₀ (orbit w₀ 0 (D.N + k + 1)) = 0 := by
    simpa [hlevel] using hpow0
  exact hnonzero hpow0'

lemma ParameterCriticalOrbitLocalBranchData.canonicalTransition_eq_quotient
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL0 : D0.N ≤ L) (hL1 : D1.N ≤ L) :
    D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 = D1.G w₀ / D0.G w₀ := rfl

lemma ParameterCriticalOrbitLocalBranchData.canonicalTransition_mem_rootsOfUnitySet
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL0 : D0.N ≤ L) (hL1 : D1.N ≤ L) :
    D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 ∈ rootsOfUnitySet (2 ^ L) := by
  rcases D0.overlap_transition_common_level D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 with ⟨η, hη, hηeq⟩
  have hG0w_ne : D0.G w₀ ≠ 0 := branch_nonzero_at_common_level D0 hW_sub0 hw₀ hL0
  have hquot : D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 = η := by
    dsimp [ParameterCriticalOrbitLocalBranchData.canonicalTransition]
    rw [hηeq w₀ hw₀]
    field_simp [hG0w_ne]
  simpa [hquot] using hη

lemma ParameterCriticalOrbitLocalBranchData.canonicalTransition_eq_on
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL0 : D0.N ≤ L) (hL1 : D1.N ≤ L) :
    ∀ c ∈ W,
      D1.G c =
        D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 * D0.G c := by
  intro c hc
  rcases D0.overlap_transition_common_level D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 with ⟨η, _hη, hηeq⟩
  have hcan : D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 = η := by
    have hG0w_ne : D0.G w₀ ≠ 0 := branch_nonzero_at_common_level D0 hW_sub0 hw₀ hL0
    dsimp [ParameterCriticalOrbitLocalBranchData.canonicalTransition]
    rw [hηeq w₀ hw₀]
    field_simp [hG0w_ne]
  rw [hcan]
  exact hηeq c hc

lemma ParameterCriticalOrbitLocalBranchData.canonicalTransition_unique
    {c₀ c₁ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL0 : D0.N ≤ L) (hL1 : D1.N ≤ L)
    {ξ : ℂ}
    (hξ : ∀ c ∈ W, D1.G c = ξ * D0.G c) :
    ξ = D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 := by
  have hG0w_ne : D0.G w₀ ≠ 0 := branch_nonzero_at_common_level D0 hW_sub0 hw₀ hL0
  dsimp [ParameterCriticalOrbitLocalBranchData.canonicalTransition]
  rw [hξ w₀ hw₀]
  field_simp [hG0w_ne]

lemma ParameterCriticalOrbitLocalBranchData.canonicalTransition_cocycle
    {c₀ c₁ c₂ : ℂ}
    (D0 : ParameterCriticalOrbitLocalBranchData c₀)
    (D1 : ParameterCriticalOrbitLocalBranchData c₁)
    (D2 : ParameterCriticalOrbitLocalBranchData c₂)
    {W : Set ℂ}
    (hW_pre : IsPreconnected W)
    (hW_sub0 : W ⊆ D0.V)
    (hW_sub1 : W ⊆ D1.V)
    (hW_sub2 : W ⊆ D2.V)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W)
    {L : ℕ} (hL0 : D0.N ≤ L) (hL1 : D1.N ≤ L) (hL2 : D2.N ≤ L) :
    D0.canonicalTransition D2 hW_pre hW_sub0 hW_sub2 hw₀ hL0 hL2 =
      D1.canonicalTransition D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 *
        D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 := by
  have h01 := D0.canonicalTransition_eq_on D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 w₀ hw₀
  have h12 := D1.canonicalTransition_eq_on D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 w₀ hw₀
  have h02 := D0.canonicalTransition_eq_on D2 hW_pre hW_sub0 hW_sub2 hw₀ hL0 hL2 w₀ hw₀
  have hG0w_ne : D0.G w₀ ≠ 0 := branch_nonzero_at_common_level D0 hW_sub0 hw₀ hL0
  have hcomp : D2.G w₀ =
      (D1.canonicalTransition D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 *
        D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1) * D0.G w₀ := by
    calc
      D2.G w₀ = D1.canonicalTransition D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 * D1.G w₀ := h12
      _ = D1.canonicalTransition D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 *
            (D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1 * D0.G w₀) := by rw [h01]
      _ = (D1.canonicalTransition D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 *
            D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1) * D0.G w₀ := by
            ring_nf
  have hfinal :
      D0.canonicalTransition D2 hW_pre hW_sub0 hW_sub2 hw₀ hL0 hL2 * D0.G w₀ =
        (D1.canonicalTransition D2 hW_pre hW_sub1 hW_sub2 hw₀ hL1 hL2 *
          D0.canonicalTransition D1 hW_pre hW_sub0 hW_sub1 hw₀ hL0 hL1) * D0.G w₀ := by
    exact h02.symm.trans hcomp
  exact mul_right_cancel₀ hG0w_ne hfinal

structure ParameterLoopSubdivisionComparisonGap where
  message : String

noncomputable def parameterLoopSubdivisionComparisonGap : ParameterLoopSubdivisionComparisonGap :=
  ⟨"Current ParameterPathMeshChain data only packages pairwise adjacent overlaps via overlap_transition_data. It does not yet provide a connected triple-overlap set, nor an explicit refinement-comparison witness linking one coarse edge to two refined edges. Therefore the one-edge subdivision product identity needed for refinement comparison is not currently derivable from the checked API alone."⟩

end MLC.Quadratic
