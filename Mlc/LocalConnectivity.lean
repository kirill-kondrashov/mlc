import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic Complex Topology Set Filter

/-- Local connectedness at one point, expressed by connected neighborhoods. -/
def LocallyConnectedAt (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected V

/-- Pointwise local connectedness implies a locally connected space. -/
lemma locallyConnectedSpace_of_locallyConnectedAt {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, LocallyConnectedAt X x) : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x _
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyF : y ∈ F := connectedComponentIn_subset F x hy
  have h_nhds : F ∈ 𝓝 y := hF.mem_nhds hyF
  obtain ⟨V, hV_nhds, hV_sub, hV_conn⟩ := h y F h_nhds
  filter_upwards [hV_nhds] with z hz
  have hy_in_V : y ∈ V := mem_of_mem_nhds hV_nhds
  have hV_sub_comp : V ⊆ connectedComponentIn F y :=
    IsPreconnected.subset_connectedComponentIn hV_conn.isPreconnected hy_in_V hV_sub
  have h_eq : connectedComponentIn F y = connectedComponentIn F x :=
    (connectedComponentIn_eq hy).symm
  rw [← h_eq]
  exact hV_sub_comp hz

/-- Connectedness is preserved by the subtype inclusion, in both directions. -/
lemma isConnected_subtype_val_image {X : Type*} [TopologicalSpace X] {p : X → Prop}
    (s : Set { x // p x }) :
    IsConnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsConnected s := by
  classical
  have h_pre :
      IsPreconnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsPreconnected s :=
    Topology.IsInducing.isPreconnected_image (s := s)
      (f := (Subtype.val : { x // p x } → X))
      (IsEmbedding.subtypeVal.isInducing)
  constructor
  · intro h
    refine ⟨?_, h_pre.1 h.2⟩
    rcases h.1 with ⟨x, ⟨y, hy, rfl⟩⟩
    exact ⟨y, hy⟩
  · intro h
    refine ⟨?_, h_pre.2 h.2⟩
    rcases h.1 with ⟨y, hy⟩
    exact ⟨Subtype.val y, ⟨y, hy, rfl⟩⟩

lemma para_puzzle_piece_induced_connected_of_at
    (c : ℂ)
    (h_conn_at : ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet))
    (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } := by
  rw [← isConnected_subtype_val_image]
  rw [show { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } =
        (Subtype.val : MandelbrotSet → ℂ) ⁻¹' (ParaPuzzlePieceAt c n) by rfl]
  rw [Subtype.image_preimage_coe]
  try rw [Set.inter_comm]
  exact h_conn_at n

lemma para_puzzle_piece_basis_induced (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : MandelbrotSet), ∃ n,
      { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } ⊆ U := by
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨V, hV_sub_U, hV_open, hc_in_V⟩ := hU
  obtain ⟨W, hW_open, hW_eq⟩ := isOpen_induced_iff.mp hV_open
  rw [← hW_eq] at hc_in_V hV_sub_U
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis c h W
    (hW_open.mem_nhds hc_in_V)
  use n
  intro x hx
  apply hV_sub_U
  exact hn_sub hx

/-- Shrinking connected parameter pieces give local connectedness at `c`. -/
lemma lc_at_of_shrink_of_connected_at
    (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h_conn_at : ∀ n, IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet))
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  rw [LocallyConnectedAt]
  intro U hU
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis_induced c hc h U hU
  let V := {x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n}
  refine ⟨V, ?_, hn_sub, ?_⟩
  · rw [mem_nhds_iff]
    refine ⟨V, subset_rfl, ?_, ?_⟩
    · rw [isOpen_induced_iff]
      exact ⟨ParaPuzzlePieceAt c n, para_puzzle_piece_open c n, rfl⟩
    · have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePieceAt c k := by
        rw [h]
        exact Set.mem_singleton c
      exact Set.mem_iInter.mp hc_in_inter n
  · exact para_puzzle_piece_induced_connected_of_at c h_conn_at n

end MLC
