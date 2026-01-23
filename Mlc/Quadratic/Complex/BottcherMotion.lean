import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Analysis.Complex.Basic

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-- A placeholder for the Böttcher coordinate depending on parameter `c`. -/
structure BottcherData where
  /-- `phi c z` is the Böttcher coordinate for the map `f_c`. -/
  phi : ℂ → ℂ → ℂ

  /-- For each `z`, the map `c ↦ phi c z` is holomorphic on the unit disk. -/
  holo_in_param : ∀ z : ℂ, DifferentiableOn ℂ (fun c => phi c z) (Metric.ball 0 1)

  /-- Normalization at the base parameter (placeholder). -/
  phi_at_zero : ∀ z : ℂ, phi 0 z = z

  /-- Injectivity of the Böttcher coordinate on the unit disk (placeholder). -/
  inj_on : ∀ t ∈ Metric.ball 0 1, Set.InjOn (phi t) Set.univ

/-- The equipotential of level `n` under a Böttcher coordinate. -/
def equipotential (B : BottcherData) (c : ℂ) (n : ℕ) : Set ℂ :=
  {z | ‖B.phi c z‖ = (1 / 2) ^ n}

/-- The induced motion from a Böttcher coordinate: move points by varying `c`. -/
def bottcher_motion (B : BottcherData) (E : Set ℂ) : HolomorphicMotion E :=
  { f := fun t z => B.phi t z
    h_zero := by
      intro z hz
      simpa using (B.phi_at_zero z)
    h_inj := by
      intro t ht
      intro x hx y hy hxy
      exact (B.inj_on t ht) (by trivial) (by trivial) hxy
    h_holo := by
      intro z hz
      simpa using (B.holo_in_param z) }

/-- Data needed to build a puzzle-boundary motion from a Böttcher coordinate. -/
structure BottcherMotionData (n : ℕ) (c₀ : ℂ) where
  B : BottcherData
  r : ℝ
  r_pos : 0 < r
  E : Set ℂ
  E_eq : E = PuzzleBoundary c₀ n
  preserves :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E)

/-- If the parameter disk stays inside the puzzle piece, then the motion preserves
    parameter puzzle membership. -/
theorem motion_preserves_para_piece_of_bottcher
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (B : BottcherData) (E : Set ℂ)
    (h_piece : ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ ParaPuzzlePiece n) :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E) := by
  intro _ _ t ht
  exact h_piece t ht

/-- If Green sublevel sets are connected and contain both `0` and the parameter,
    then the Böttcher motion preserves parameter puzzle membership. -/
theorem motion_preserves_para_piece_of_green_sublevel
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (B : BottcherData) (E : Set ℂ)
    (h0 : ∀ t ∈ Metric.ball 0 1, 0 ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hmem : ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hconn : ∀ t ∈ Metric.ball 0 1, IsConnected (GreenSublevel (rescale_param c₀ r t) n)) :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E) := by
  intro _ _ t ht
  exact
    para_puzzle_piece_of_sublevel_connected (rescale_param c₀ r t) n
      (h0 t ht) (hmem t ht) (hconn t ht)

/-- Turn Böttcher-based motion data into the generic puzzle-boundary motion data. -/
def puzzle_boundary_motion_data_of_bottcher (n : ℕ) (c₀ : ℂ)
    (h : BottcherMotionData n c₀) : PuzzleBoundaryMotionData n c₀ := by
  refine
    { r := h.r
      r_pos := h.r_pos
      E := h.E
      motion := bottcher_motion h.B h.E
      preserves := h.preserves }

end
end MLC.Quadratic
