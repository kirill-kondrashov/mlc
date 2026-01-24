import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mlc.Quadratic.Complex.ParaPuzzle
import Mathlib.Topology.Connected.LocallyConnected
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
lemma isConnected_subtype_val_image {X : Type*} [TopologicalSpace X] {p : X → Prop}
    (s : Set { x // p x }) :
    IsConnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsConnected s := by
  classical
  -- First reduce to preconnectedness using the general theorem for inducing maps.
  have h_pre :
      IsPreconnected ((Subtype.val : { x // p x } → X) '' s) ↔ IsPreconnected s :=
    Topology.IsInducing.isPreconnected_image (s := s)
      (f := (Subtype.val : { x // p x } → X))
      (IsEmbedding.subtypeVal.isInducing)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- Nonemptiness transfers from the image back to the subtype.
      rcases h.1 with ⟨x, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨y, hy⟩
    · -- And preconnectedness is equivalent by `isPreconnected_image`.
      exact h_pre.1 h.2
  · intro h
    refine ⟨?_, ?_⟩
    · -- Nonemptiness transfers from the subtype to the image.
      rcases h.1 with ⟨y, hy⟩
      exact ⟨Subtype.val y, ⟨y, hy, rfl⟩⟩
    · exact h_pre.2 h.2

/-- The intersection of a parameter puzzle piece with the Mandelbrot set is connected in the subtype topology. -/
lemma para_puzzle_piece_induced_connected (c : ℂ) (n : ℕ) :
    IsConnected { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } := by
  rw [← isConnected_subtype_val_image]
  rw [show { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } =
        (Subtype.val : MandelbrotSet → ℂ) ⁻¹' (ParaPuzzlePieceAt c n) by rfl]
  rw [Subtype.image_preimage_coe]
  try rw [Set.inter_comm]
  exact para_puzzle_piece_inter_mandelbrot_connected c n

/-- If parameter pieces shrink to a point, they form a basis of neighborhoods for c in the Mandelbrot set.
    Proof idea: Since the intersection of all parameter pieces `ParaPuzzlePieceAt c n` is exactly `{c}`,
    for any open neighborhood `U` of `c`, there must be some `n` such that `ParaPuzzlePieceAt c n ⊆ U`.
    This uses the compactness argument implicit in the "shrink to point" property for nested compact sets
    (or similar topological argument). Here we formalize it by showing `M ∩ P_n` eventually lies in `U`. -/
lemma para_puzzle_piece_basis_induced (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 (⟨c, hc⟩ : MandelbrotSet), ∃ n,
      { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n } ⊆ U := by
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

/-- If parameter pieces shrink to a point, M is locally connected at c.
    Proof idea: We construct a basis of connected neighborhoods for `c`.
    1.  The parameter pieces `P_n` are open (by `para_puzzle_piece_open`).
    2.  Their intersection with `M` is connected (by `para_puzzle_piece_induced_connected`).
    3.  They shrink to `{c}` (hypothesis).
    4.  Therefore, for any neighborhood `U`, we can find a `P_n` inside it. `P_n ∩ M` serves
        as the connected neighborhood of `c` contained in `U`, proving local connectivity. -/
lemma lc_at_of_shrink (c : ℂ) (hc : c ∈ MandelbrotSet)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  rw [LocallyConnectedAt]
  intro U hU
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis_induced c hc h U hU
  let V' := { x : MandelbrotSet | x.val ∈ ParaPuzzlePieceAt c n }
  use V'
  constructor
  · -- V' ∈ 𝓝 ⟨c, hc⟩
    rw [mem_nhds_iff]
    use V'
    constructor
    · exact subset_rfl
    · constructor
      · rw [isOpen_induced_iff]
        use ParaPuzzlePieceAt c n
        constructor
        · exact para_puzzle_piece_open c n
        · rfl
      · have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePieceAt c k := by
          rw [h]
          exact Set.mem_singleton c
        exact Set.mem_iInter.mp hc_in_inter n
  · constructor
    · exact hn_sub
    · exact para_puzzle_piece_induced_connected c n

end MLC
