import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Puzzle
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

/-- If parameter pieces shrink to a point, M is locally connected at c. -/
lemma lc_at_of_shrink (c : ℂ) (hc : c ∈ MandelbrotSet) (h : (⋂ n, ParaPuzzlePiece n) = {c}) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := by
  rw [LocallyConnectedAt]
  intro U hU
  -- U is a neighborhood of c in MandelbrotSet
  rw [mem_nhds_iff] at hU
  obtain ⟨V, hV_sub_U, hV_open, hc_in_V⟩ := hU
  -- V is open in MandelbrotSet, so V = W ∩ MandelbrotSet for some W open in ℂ
  obtain ⟨W, hW_open, hW_eq⟩ := isOpen_induced_iff.mp hV_open
  rw [← hW_eq] at hc_in_V hV_sub_U

  -- c ∈ W and W is open
  have hc_in_W : c ∈ W := hc_in_V
  have hW_nhds : W ∈ 𝓝 c := hW_open.mem_nhds hc_in_W

  -- Use para_puzzle_piece_basis to find a piece inside W
  obtain ⟨n, hn_sub⟩ := para_puzzle_piece_basis c h W hW_nhds

  let P := ParaPuzzlePiece n
  let V' := (Subtype.val : MandelbrotSet → ℂ) ⁻¹' P

  use V'
  constructor
  · -- V' ∈ 𝓝 ⟨c, hc⟩
    rw [mem_nhds_iff]
    have hV'_open : IsOpen V' := by
      rw [isOpen_induced_iff]
      use P
      constructor
      · exact para_puzzle_piece_open n
      · rfl
    use V'
    constructor
    · exact subset_rfl
    · constructor
      · exact hV'_open
      · -- c ∈ P
        have hc_in_inter : c ∈ ⋂ k, ParaPuzzlePiece k := by rw [h]; exact Set.mem_singleton c
        exact Set.mem_iInter.mp hc_in_inter n

  constructor
  · -- V' ⊆ U
    intro x hx
    apply hV_sub_U
    exact hn_sub hx

  · -- IsConnected V'
    have h_conn : IsConnected (P ∩ MandelbrotSet) := para_puzzle_piece_inter_mandelbrot_connected n
    -- V' is homeomorphic to P ∩ MandelbrotSet, so it is connected.
    -- TODO: Prove homeomorphism and use it.
    sorry

end MLC
