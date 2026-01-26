import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.Basic

namespace MLC.Quadratic

open Complex Topology Set Filter Metric

/-!
# Structured Proof of `motion_preserves_para_piece_of_green_sublevel`

This file breaks down the axiom `motion_preserves_para_piece_of_green_sublevel` into
smaller, provable lemmas.
-/

/-- Step 1: Identification of the dynamical puzzle piece when the sublevel set is connected. -/
lemma dynamical_puzzle_piece_eq_green_sublevel (c : ℂ) (n : ℕ) (z : ℂ)
    (hconn : IsConnected (GreenSublevel c n)) (hz : z ∈ GreenSublevel c n) :
    DynamicalPuzzlePiece c n z = GreenSublevel c n := by
  rw [DynamicalPuzzlePiece]
  apply subset_antisymm
  · exact connectedComponentIn_subset _ _
  · exact hconn.isPreconnected.subset_connectedComponentIn hz subset_rfl

/-- Step 1b: Membership of a point in its own dynamical puzzle piece under the connectedness hypothesis. -/
lemma mem_dynamical_puzzle_piece_of_connected (c : ℂ) (n : ℕ) (z w : ℂ)
    (hconn : IsConnected (GreenSublevel c n)) (hz : z ∈ GreenSublevel c n) (hw : w ∈ GreenSublevel c n) :
    w ∈ DynamicalPuzzlePiece c n z := by
  rw [dynamical_puzzle_piece_eq_green_sublevel c n z hconn hz]
  exact hw

/-- Step 2: Boundary Stability. The Böttcher motion preserves the puzzle boundary. -/
lemma bottcher_motion_preserves_boundary (B : BottcherData) (c₀ : ℂ) (n : ℕ) (t : ℂ) (ht : t ∈ ball 0 1) :
    (bottcher_motion B (PuzzleBoundary c₀ n)).f t '' (PuzzleBoundary c₀ n) = PuzzleBoundary (rescale_param c₀ 1 t) n := by
  let c_t := rescale_param c₀ 1 t
  
  -- Use the homeomorphism axiom
  obtain ⟨h_t, hh_t⟩ := bottcher_motion_homeomorph B t ht
  
  -- PuzzleBoundary c n = frontier {w | green_function c w < (1 / 2) ^ n}
  let S₀ := {w | green_function c₀ w < (1 / 2) ^ n}
  let S_t := {w | green_function c_t w < (1 / 2) ^ n}
  
  have h_S : h_t '' S₀ = S_t := by
    ext w
    constructor
    · rintro ⟨z, (hz : green_function c₀ z < (1 / 2) ^ n), rfl⟩
      show green_function c_t (h_t z) < (1 / 2) ^ n
      have : h_t z = B.phi t z := by rw [← hh_t]; rfl
      rw [this, green_invariant_under_bottcher_motion B c₀ 1 t ht z]
      exact hz
    · intro (hw : green_function c_t w < (1 / 2) ^ n)
      use h_t.symm w
      constructor
      · show green_function c₀ (h_t.symm w) < (1 / 2) ^ n
        rw [← green_invariant_under_bottcher_motion B c₀ 1 t ht]
        have : B.phi t (h_t.symm w) = h_t (h_t.symm w) := by rw [← hh_t]; rfl
        rw [this, h_t.apply_symm_apply]
        exact hw
      · exact h_t.apply_symm_apply w
  
  rw [PuzzleBoundary, PuzzleBoundary]
  have h_f_img : (bottcher_motion B (frontier S₀)).f t '' frontier S₀ = h_t '' frontier S₀ := by
    apply image_congr
    intro z _
    dsimp [bottcher_motion]
    rw [← hh_t]
    rfl
  rw [h_f_img]
  rw [h_t.image_frontier]
  rw [h_S]

/-- Step 3: Invariance of the piece under motion.
    The image of the puzzle piece under the extended holomorphic motion is the puzzle piece at time t. -/
lemma motion_maps_piece_to_piece (n : ℕ) (c₀ : ℂ) (r : ℝ) (E : Set ℂ) (h : HolomorphicMotion E)
    (H : HolomorphicMotion Set.univ) (h_ext : ∀ t ∈ ball 0 1, ∀ z ∈ E, H.f t z = h.f t z)
    (t : ℂ) (ht : t ∈ ball 0 1) :
    H.f t '' (DynamicalPuzzlePiece c₀ n 0) = DynamicalPuzzlePiece (rescale_param c₀ r t) n 0 := by
  sorry

/-- Step 4: Parameter-Dynamics Correspondence.
    If the critical value is trapped in the moving dynamical piece, the parameter is in the para-puzzle piece. -/
theorem motion_preserves_para_piece_of_green_sublevel_structured
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (B : BottcherData) (E : Set ℂ)
    (h0 : ∀ t ∈ ball 0 1, 0 ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hmem : ∀ t ∈ ball 0 1, rescale_param c₀ r t ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hconn : ∀ t ∈ ball 0 1, IsConnected (GreenSublevel (rescale_param c₀ r t) n)) :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E) := by
  intro H h_ext t ht
  let c_t := rescale_param c₀ r t
  rw [ParaPuzzlePieceAt, mem_setOf_eq]
  -- We need to show c_t - c₀ ∈ DynamicalPuzzlePiece c₀ n 0.
  -- This requires the correspondence between parameter piece and dynamical piece.
  sorry

end MLC.Quadratic
