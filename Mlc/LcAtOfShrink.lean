import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Puzzle
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Lean

open Lean Elab Command

namespace MLC

open Quadratic Complex Topology Set Filter

/-- Local connectivity at a point in a topological space. -/
def LocallyConnectedAt (X : Type*) [TopologicalSpace X] (x : X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected V

/-- If a space is locally connected at every point, it is a locally connected space. -/
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

/-- A set in a subtype is connected iff its image in the ambient space is connected. -/
lemma isConnected_image_of_embedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) (s : Set X) :
    IsConnected (f '' s) ↔ IsConnected s := by
  let f' : s → Y := f ∘ Subtype.val
  have h_emb : IsEmbedding f' := hf.comp IsEmbedding.subtypeVal
  let e : s ≃ₜ Set.range f' := h_emb.toHomeomorph
  have h_range : Set.range f' = f '' s := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Function.comp_apply, Subtype.exists, exists_prop, f']
  rw [← h_range]

  constructor
  · rintro ⟨h_non, h_pre⟩
    refine ⟨?_, ?_⟩
    · -- s.Nonempty
      exact Set.nonempty_coe_sort.mp (h_non.to_subtype.map e.symm)
    · -- IsPreconnected s
      rw [isPreconnected_iff_preconnectedSpace] at h_pre ⊢
      apply PreconnectedSpace.mk
      have h_ind := e.symm.isInducing
      rw [← Set.image_univ_of_surjective (Homeomorph.surjective e.symm)]
      rw [h_ind.isPreconnected_image]
      exact @PreconnectedSpace.isPreconnected_univ _ _ h_pre
  · rintro ⟨h_non, h_pre⟩
    refine ⟨?_, ?_⟩
    · -- (range f').Nonempty
      exact Set.nonempty_coe_sort.mp (h_non.to_subtype.map e)
    · -- IsPreconnected (range f')
      rw [isPreconnected_iff_preconnectedSpace] at h_pre ⊢
      apply PreconnectedSpace.mk
      have h_ind := e.isInducing
      rw [← Set.image_univ_of_surjective (Homeomorph.surjective e)]
      rw [h_ind.isPreconnected_image]
      exact @PreconnectedSpace.isPreconnected_univ _ _ h_pre

lemma isConnected_subtype_val_image {X : Type*} [TopologicalSpace X] {p : X → Prop}
    (s : Set { x // p x }) :
    IsConnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsConnected s := by
  let f := (Subtype.val : { x // p x } → X)
  have h_emb : IsEmbedding f := IsEmbedding.subtypeVal
  exact isConnected_image_of_embedding h_emb s

/-- The intersection of a parameter puzzle piece with the Mandelbrot set is connected in the subtype topology. -/
lemma para_puzzle_piece_induced_connected (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePiece n } := by
  rw [← isConnected_subtype_val_image]
  have h_img : (Subtype.val : MandelbrotSet → ℂ) '' { x : MandelbrotSet | x.val ∈ ParaPuzzlePiece n } =
      ParaPuzzlePiece n ∩ MandelbrotSet := by
    ext z
    constructor
    · intro h
      rcases h with ⟨x, hx, rfl⟩
      exact ⟨hx, x.property⟩
    · intro h
      rcases h with ⟨hP, hM⟩
      use ⟨z, hM⟩
      constructor
      · exact hP
      · rfl
  rw [h_img]
  exact para_puzzle_piece_inter_mandelbrot_connected n

/-- If parameter pieces shrink to a point, they form a basis of neighborhoods for c in the Mandelbrot set. -/
lemma para_puzzle_piece_basis_induced (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePiece n) = {c}) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : MandelbrotSet), ∃ n, { x : MandelbrotSet | x.val ∈ ParaPuzzlePiece n } ⊆ U := by
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨V, hV_sub_U, hV_open, hc_in_V⟩ := hU
  obtain ⟨W, hW_open, hW_eq⟩ := isOpen_induced_iff.mp hV_open
  rw [← hW_eq] at hc_in_V hV_sub_U
  have hc_in_W : c ∈ W := hc_in_V
  have hW_nhds : W ∈ 𝓝 c := hW_open.mem_nhds hc_in_W
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis c h W hW_nhds
  use n
  intro x hx
  apply hV_sub_U
  exact hn_sub hx

/-- If parameter pieces shrink to a point, M is locally connected at c. -/
lemma lc_at_of_shrink (c : ℂ) (hc : c ∈ MandelbrotSet) (h : (⋂ n, ParaPuzzlePiece n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  rw [LocallyConnectedAt]
  intro U hU
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis_induced c hc h U hU
  let V' := { x : MandelbrotSet | x.val ∈ ParaPuzzlePiece n }
  use V'
  constructor
  · -- V' ∈ 𝓝 ⟨c, hc⟩
    rw [mem_nhds_iff]
    use V'
    constructor
    · exact subset_rfl
    · constructor
      · rw [isOpen_induced_iff]
        use ParaPuzzlePiece n
        constructor
        · exact para_puzzle_piece_open n
        · rfl
      · have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePiece k := by rw [h]; exact Set.mem_singleton c
        exact Set.mem_iInter.mp hc_in_inter n
  · constructor
    · exact hn_sub
    · exact para_puzzle_piece_induced_connected n

end MLC
