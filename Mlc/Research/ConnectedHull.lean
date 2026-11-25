import Mathlib

/-!
# Minimal connected hulls of compact continua

This is the generic topological component of the connected-hull language used
in the virtual-Julia programme. No quadratic dynamics is assumed here.
-/

namespace MLC.Research

open Set Filter Topology

noncomputable section

theorem directed_intersection_continuum
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {S : Set (Set X)} (hSne : S.Nonempty)
    (hSd : DirectedOn (· ⊇ ·) S)
    (hSc : ∀ s ∈ S, IsCompact s)
    (hSconn : ∀ s ∈ S, IsConnected s) :
    IsCompact (⋂₀ S) ∧ IsConnected (⋂₀ S) := by
  classical
  letI : Nonempty S := hSne.to_subtype
  have hsclosed : ∀ s ∈ S, IsClosed s := fun s hs => (hSc s hs).isClosed
  have hIntClosed : IsClosed (⋂₀ S) := isClosed_sInter hsclosed
  obtain ⟨K0, hK0⟩ := hSne
  have hIntCompact : IsCompact (⋂₀ S) :=
    (hSc K0 hK0).of_isClosed_subset hIntClosed (sInter_subset_of_mem hK0)
  have hIntNE : (⋂₀ S).Nonempty :=
    IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
      hSd (fun U hU => (hSconn U hU).nonempty) hSc hsclosed
  refine ⟨hIntCompact, hIntNE, ?_⟩
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed hIntClosed).2
  intro u v hu hv hcover huv
  by_contra hn
  have hnU : ¬ (⋂₀ S) ⊆ u := fun h => hn (Or.inl h)
  have hnV : ¬ (⋂₀ S) ⊆ v := fun h => hn (Or.inr h)
  obtain ⟨x, hxS, hxnotU⟩ := Set.not_subset.mp hnU
  have hxV : x ∈ v := (hcover hxS).resolve_left hxnotU
  obtain ⟨y, hyS, hynotV⟩ := Set.not_subset.mp hnV
  have hyU : y ∈ u := (hcover hyS).resolve_right hynotV
  have hleft : IsCompact ((⋂₀ S) ∩ u) := hIntCompact.inter_right hu
  have hright : IsCompact ((⋂₀ S) ∩ v) := hIntCompact.inter_right hv
  have hdisj : Disjoint ((⋂₀ S) ∩ u) ((⋂₀ S) ∩ v) :=
    huv.mono inter_subset_right inter_subset_right
  obtain ⟨U, V, hU, hV, hUsub, hVsub, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hleft hright hdisj
  have hICover : (⋂₀ S) ⊆ U ∪ V := by
    intro z hz
    rcases hcover hz with hzu | hzv
    · exact Or.inl (hUsub ⟨hz, hzu⟩)
    · exact Or.inr (hVsub ⟨hz, hzv⟩)
  have hUnhds : ∀ z ∈ ⋂ i : S, (i : Set X), U ∪ V ∈ 𝓝 z := by
    intro z hz
    apply (hU.union hV).mem_nhds
    apply hICover
    rwa [sInter_eq_iInter]
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact hSd.directed_val
    (fun i : S => hSc i i.2) hUnhds
  have hxI : x ∈ (i : Set X) := (sInter_subset_of_mem i.2) hxS
  have hyI : y ∈ (i : Set X) := (sInter_subset_of_mem i.2) hyS
  have hxVn : x ∈ V := hVsub ⟨hxS, hxV⟩
  have hyUn : y ∈ U := hUsub ⟨hyS, hyU⟩
  obtain ⟨z, hzI, hzU, hzV⟩ :=
    (hSconn i i.2).isPreconnected U V hU hV hi ⟨y, hyI, hyUn⟩ ⟨x, hxI, hxVn⟩
  exact (Set.disjoint_left.mp hUV) hzU hzV

/-- A compact connected hull of `A` in `C` that is inclusion-minimal. -/
theorem exists_minimal_connected_hull
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C A : Set X} (hCcompact : IsCompact C) (hCconn : IsConnected C)
    (_hA : A.Nonempty) (hAC : A ⊆ C) :
    ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ A ⊆ K ∧ K ⊆ C ∧
      ∀ L : Set X, IsCompact L → IsConnected L → A ⊆ L → L ⊆ K → L = K := by
  classical
  let S : Set (Set X) :=
    {K | IsCompact K ∧ IsConnected K ∧ A ⊆ K ∧ K ⊆ C}
  have hC : C ∈ S := ⟨hCcompact, hCconn, hAC, subset_rfl⟩
  have chain_lower :
      ∀ T ⊆ S, IsChain (· ⊆ ·) T → T.Nonempty →
        ∃ I ∈ S, ∀ K ∈ T, I ⊆ K := by
    intro T hTS hchain hTnon
    have hchainRev : IsChain (· ⊇ ·) T := hchain.symm
    have hdir : DirectedOn (· ⊇ ·) T := hchainRev.directedOn
    have hcompact : ∀ K ∈ T, IsCompact K := fun K hK => (hTS hK).1
    have hconn : ∀ K ∈ T, IsConnected K := fun K hK => (hTS hK).2.1
    obtain ⟨hIcompact, hIconn⟩ :=
      directed_intersection_continuum hTnon hdir hcompact hconn
    refine ⟨⋂₀ T, ?_, ?_⟩
    · refine ⟨hIcompact, hIconn, ?_, ?_⟩
      · exact subset_sInter fun K hK => (hTS hK).2.2.1
      · obtain ⟨K, hK⟩ := hTnon
        exact (sInter_subset_of_mem hK).trans ((hTS hK).2.2.2)
    · exact fun K hK => sInter_subset_of_mem hK
  obtain ⟨K, hKC, hKmin⟩ := zorn_superset_nonempty S chain_lower C hC
  refine ⟨K, hKmin.1.1, hKmin.1.2.1, hKmin.1.2.2.1, hKC, ?_⟩
  intro L hLcompact hLconn hAL hLK
  have hLC : L ⊆ C := hLK.trans hKC
  exact hKmin.eq_of_subset ⟨hLcompact, hLconn, hAL, hLC⟩ hLK

end

end MLC.Research
