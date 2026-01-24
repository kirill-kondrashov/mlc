import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Analysis.Complex.Basic

set_option linter.unnecessarySimpa false

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
      intro t ht x hx y hy hxy
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

/-- Global hypothesis providing Böttcher-based motion data for all parameters. -/
structure BottcherMotionHyp where
  data : ∀ (n : ℕ) (c₀ : ℂ), BottcherMotionData n c₀

/-- If the parameter disk stays inside the puzzle piece, then the motion preserves
    parameter puzzle membership. -/
theorem motion_preserves_para_piece_of_bottcher
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (B : BottcherData) (E : Set ℂ)
    (h_piece : ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ ParaPuzzlePieceAt c₀ n) :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E) := by
  intro _ _ t ht
  exact h_piece t ht

/-- Green-sublevel control yields parameter-piece preservation (axiom). -/
axiom motion_preserves_para_piece_of_green_sublevel
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (B : BottcherData) (E : Set ℂ)
    (h0 : ∀ t ∈ Metric.ball 0 1, 0 ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hmem : ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hconn : ∀ t ∈ Metric.ball 0 1, IsConnected (GreenSublevel (rescale_param c₀ r t) n)) :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E)

/-- Turn Böttcher-based motion data into the generic puzzle-boundary motion data. -/
def puzzle_boundary_motion_data_of_bottcher (n : ℕ) (c₀ : ℂ)
    (h : BottcherMotionData n c₀) : PuzzleBoundaryMotionData n c₀ := by
  refine
    { r := h.r
      r_pos := h.r_pos
      E := h.E
      motion := bottcher_motion h.B h.E
      preserves := h.preserves }

/-- Produce the boundary motion hypothesis from Böttcher-based data. -/
def puzzle_boundary_motion_hyp_of_bottcher (h : BottcherMotionHyp) :
    PuzzleBoundaryMotionHyp :=
  { motion := fun n c₀ _hc₀ =>
      puzzle_boundary_motion_exists_of_data n c₀
        (puzzle_boundary_motion_data_of_bottcher n c₀ (h.data n c₀)) }

/-- Build Böttcher motion data from Green sublevel hypotheses. -/
def bottcher_motion_data_of_green_sublevel (n : ℕ) (c₀ : ℂ) (B : BottcherData)
    (r : ℝ) (r_pos : 0 < r)
    (h0 : ∀ t ∈ Metric.ball 0 1, 0 ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hmem : ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hconn : ∀ t ∈ Metric.ball 0 1, IsConnected (GreenSublevel (rescale_param c₀ r t) n)) :
    BottcherMotionData n c₀ := by
  refine
    { B := B
      r := r
      r_pos := r_pos
      E := PuzzleBoundary c₀ n
      E_eq := rfl
      preserves :=
        motion_preserves_para_piece_of_green_sublevel n c₀ r B (PuzzleBoundary c₀ n)
          h0 hmem hconn }

/-- Global hypothesis: Green sublevel control for every parameter and depth. -/
structure BottcherGreenSublevelHyp where
  B : ℕ → ℂ → BottcherData
  r : ℕ → ℂ → ℝ
  r_pos : ∀ n c₀, 0 < r n c₀
  h0 : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    0 ∈ GreenSublevel (rescale_param c₀ (r n c₀) t) n
  hmem : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    rescale_param c₀ (r n c₀) t ∈ GreenSublevel (rescale_param c₀ (r n c₀) t) n
  hconn : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    IsConnected (GreenSublevel (rescale_param c₀ (r n c₀) t) n)

/-- Produce Böttcher motion data from Green sublevel hypotheses. -/
def bottcher_motion_hyp_of_green_sublevel (h : BottcherGreenSublevelHyp) :
    BottcherMotionHyp :=
  { data := fun n c₀ =>
      bottcher_motion_data_of_green_sublevel n c₀ (h.B n c₀) (h.r n c₀) (h.r_pos n c₀)
        (fun t ht => h.h0 n c₀ t ht)
        (fun t ht => h.hmem n c₀ t ht)
        (fun t ht => h.hconn n c₀ t ht) }

/-- A weaker hypothesis: the parameter disk stays in `M`, and sublevels are connected. -/
structure BottcherGreenSublevelHypOnM where
  B : ℕ → ℂ → BottcherData
  r : ℕ → ℂ → ℝ
  r_pos : ∀ n c₀, 0 < r n c₀
  in_M : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    rescale_param c₀ (r n c₀) t ∈ MandelbrotSet
  hconn : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    IsConnected (GreenSublevel (rescale_param c₀ (r n c₀) t) n)

/-- Hypothesis: parameter disk lies in `M`, and Green sublevels are connected on `M`. -/
structure BottcherGreenSublevelHypOnMConnected where
  B : ℕ → ℂ → BottcherData
  r : ℕ → ℂ → ℝ
  r_pos : ∀ n c₀, 0 < r n c₀
  in_M : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    rescale_param c₀ (r n c₀) t ∈ MandelbrotSet
  hconn : GreenSublevelConnectedHyp

/-- Base hypothesis: parameter disk stays in `M`. -/
structure BottcherOnMHyp where
  B : ℕ → ℂ → BottcherData
  r : ℕ → ℂ → ℝ
  r_pos : ∀ n c₀, 0 < r n c₀
  in_M : ∀ n c₀ t, t ∈ Metric.ball 0 1 →
    rescale_param c₀ (r n c₀) t ∈ MandelbrotSet

/-- Derive Green-sublevel hypotheses from Mandelbrot-set control. -/
def bottcher_green_sublevel_hyp_of_onM (h : BottcherGreenSublevelHypOnM) :
    BottcherGreenSublevelHyp :=
  { B := h.B
    r := h.r
    r_pos := h.r_pos
    h0 := fun n c₀ t ht =>
      green_sublevel_contains_0 (rescale_param c₀ (h.r n c₀) t) n (h.in_M n c₀ t ht)
    hmem := fun n c₀ t ht =>
      green_sublevel_contains_c (rescale_param c₀ (h.r n c₀) t) n (h.in_M n c₀ t ht)
    hconn := h.hconn }

/-- Derive Green-sublevel hypotheses from `M`-control and connectedness on `M`. -/
def bottcher_green_sublevel_hyp_of_onM_connected (h : BottcherGreenSublevelHypOnMConnected) :
    BottcherGreenSublevelHyp :=
  bottcher_green_sublevel_hyp_of_onM
    { B := h.B
      r := h.r
      r_pos := h.r_pos
      in_M := h.in_M
      hconn := fun n c₀ t ht =>
        h.hconn.connected (rescale_param c₀ (h.r n c₀) t) n (h.in_M n c₀ t ht) }

/-- Assemble `BottcherGreenSublevelHypOnMConnected` from separate hypotheses. -/
def bottcher_green_sublevel_hyp_onM_connected_of_onM
    (h : BottcherOnMHyp) (hconn : GreenSublevelConnectedHyp) :
    BottcherGreenSublevelHypOnMConnected :=
  { B := h.B
    r := h.r
    r_pos := h.r_pos
    in_M := h.in_M
    hconn := hconn }

/-- Produce the boundary motion hypothesis directly from Mandelbrot-set control. -/
def puzzle_boundary_motion_hyp_of_onM (h : BottcherGreenSublevelHypOnM) :
    PuzzleBoundaryMotionHyp :=
  puzzle_boundary_motion_hyp_of_bottcher
    (bottcher_motion_hyp_of_green_sublevel (bottcher_green_sublevel_hyp_of_onM h))

/-- Produce the boundary motion hypothesis from `M`-control and connectedness on `M`. -/
def puzzle_boundary_motion_hyp_of_onM_connected (h : BottcherGreenSublevelHypOnMConnected) :
    PuzzleBoundaryMotionHyp :=
  puzzle_boundary_motion_hyp_of_bottcher
    (bottcher_motion_hyp_of_green_sublevel (bottcher_green_sublevel_hyp_of_onM_connected h))

end
end MLC.Quadratic
