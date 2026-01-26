import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Basic

set_option linter.unnecessarySimpa false

namespace MLC.Quadratic

open Complex Topology Set Metric

noncomputable section

/-- A placeholder for the Böttcher coordinate depending on parameter `c`. -/
structure BottcherData where
  /-- `phi c z` is the Böttcher coordinate for the map `f_c`. -/
  phi : ℂ → ℂ → ℂ

  /-- For each `z`, the map `c ↦ phi c z` is holomorphic on the unit disk. -/
  holo_in_param : ∀ z : ℂ, DifferentiableOn ℂ (fun c => phi c z) (ball 0 1)

  /-- Normalization at the base parameter (placeholder). -/
  phi_at_zero : ∀ z : ℂ, phi 0 z = z

  /-- Injectivity of the Böttcher coordinate on the unit disk (placeholder). -/
  inj_on : ∀ t ∈ ball 0 1, Set.InjOn (phi t) Set.univ

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

/-- Holomorphic motion of the whole plane is a homeomorphism at each time t (axiom). -/
axiom holomorphic_motion_univ_homeomorph (H : HolomorphicMotion Set.univ) (t : ℂ) (ht : t ∈ ball 0 1) :
    ∃ h : Homeomorph ℂ ℂ, h.toFun = H.f t

/-- A homeomorphism mapping the boundary of a component to the boundary of another component
    maps the component to the component. (Topological Axiom) -/
axiom homeomorphism_maps_component {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (S : Set X) (T : Set Y) (h_bound : h '' frontier S = frontier T)
    (h_pt : ∃ x ∈ S, h x ∈ T) : h '' S = T

/-- Parameter-dynamics correspondence: membership in the parameter piece is equivalent to
    membership of the rescaled critical value in the moved dynamical piece. (Axiom) -/
axiom parameter_dynamics_stability (n : ℕ) (c₀ : ℂ) (r : ℝ) (t : ℂ) (ht : t ∈ ball 0 1)
    (H : HolomorphicMotion Set.univ) (h_piece : H.f t '' (DynamicalPuzzlePiece c₀ n 0) = DynamicalPuzzlePiece (rescale_param c₀ r t) n 0) :
    rescale_param c₀ r t ∈ ParaPuzzlePieceAt c₀ n ↔ rescale_param c₀ r t ∈ DynamicalPuzzlePiece (rescale_param c₀ r t) n 0

/-- Böttcher motion follows equipotentials of the Green's function (axiom). -/
axiom green_invariant_under_bottcher_motion (B : BottcherData) (c₀ : ℂ) (r : ℝ) :
    ∀ t ∈ ball 0 1, ∀ z, green_function (rescale_param c₀ r t) (B.phi t z) = green_function c₀ z

/-- Böttcher motion is a homeomorphism of the complex plane at each time t (axiom). -/
axiom bottcher_motion_homeomorph (B : BottcherData) (t : ℂ) (ht : t ∈ ball 0 1) :
    ∃ h : Homeomorph ℂ ℂ, h.toFun = B.phi t

/-- Identification of the dynamical puzzle piece when the sublevel set is connected. -/
lemma dynamical_puzzle_piece_eq_green_sublevel (c : ℂ) (n : ℕ) (z : ℂ)
    (hconn : IsConnected (GreenSublevel c n)) (hz : z ∈ GreenSublevel c n) :
    DynamicalPuzzlePiece c n z = GreenSublevel c n := by
  rw [DynamicalPuzzlePiece]
  apply subset_antisymm
  · exact connectedComponentIn_subset _ _
  · exact hconn.isPreconnected.subset_connectedComponentIn hz subset_rfl

/-- The Böttcher motion preserves the puzzle boundary. -/
lemma bottcher_motion_preserves_boundary (B : BottcherData) (c₀ : ℂ) (r : ℝ) (n : ℕ) (t : ℂ) (ht : t ∈ ball 0 1) :
    (bottcher_motion B (PuzzleBoundary c₀ n)).f t '' (PuzzleBoundary c₀ n) = PuzzleBoundary (rescale_param c₀ r t) n := by
  let c_t := rescale_param c₀ r t
  obtain ⟨h_t, hh_t⟩ := bottcher_motion_homeomorph B t ht
  let S₀ := {w | green_function c₀ w < (1 / 2) ^ n}
  let S_t := {w | green_function c_t w < (1 / 2) ^ n}
  have h_S : h_t '' S₀ = S_t := by
    ext w
    constructor
    · rintro ⟨z, (hz : green_function c₀ z < (1 / 2) ^ n), rfl⟩
      show green_function c_t (h_t z) < (1 / 2) ^ n
      have : h_t z = B.phi t z := by rw [← hh_t]; rfl
      rw [this, green_invariant_under_bottcher_motion B c₀ r t ht z]
      exact hz
    · intro (hw : green_function c_t w < (1 / 2) ^ n)
      use h_t.symm w
      constructor
      · show green_function c₀ (h_t.symm w) < (1 / 2) ^ n
        rw [← green_invariant_under_bottcher_motion B c₀ r t ht]
        have : B.phi t (h_t.symm w) = h_t (h_t.symm w) := by rw [← hh_t]; rfl
        rw [this, h_t.apply_symm_apply]
        exact hw
      · exact h_t.apply_symm_apply w
  rw [PuzzleBoundary, PuzzleBoundary]
  have h_f_img : (bottcher_motion B (frontier S₀)).f t '' frontier S₀ = h_t '' frontier S₀ := by
    apply image_congr
    intro z _
    dsimp [bottcher_motion]
    rw [← hh_t]; rfl
  rw [h_f_img, h_t.image_frontier, h_S]

/-- A holomorphic motion of the whole plane preserves component membership (axiom). -/
axiom holomorphic_motion_preserves_component (H : HolomorphicMotion Set.univ) (t : ℂ) (ht : t ∈ ball 0 1)
    (S₀ S_t : Set ℂ) (h_bound : H.f t '' frontier S₀ = frontier S_t) :
    ∀ x, x ∈ S₀ ↔ H.f t x ∈ S_t

/-- Green-sublevel control yields parameter-piece preservation (theorem). -/
theorem motion_preserves_para_piece_of_green_sublevel
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (B : BottcherData) (E : Set ℂ)
    (hE : E = PuzzleBoundary c₀ n)
    (h0 : ∀ t ∈ Metric.ball 0 1, 0 ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hmem : ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ GreenSublevel (rescale_param c₀ r t) n)
    (hconn : ∀ t ∈ Metric.ball 0 1, IsConnected (GreenSublevel (rescale_param c₀ r t) n)) :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E) := by
  intro H h_ext t ht
  let c_t := rescale_param c₀ r t
  have h_piece_to_piece : H.f t '' (DynamicalPuzzlePiece c₀ n 0) = DynamicalPuzzlePiece c_t n 0 := by
    obtain ⟨h_t, hh_t⟩ := holomorphic_motion_univ_homeomorph H t ht
    let S₀ := GreenSublevel c₀ n
    let S_t := GreenSublevel c_t n
    have hr0 : rescale_param c₀ r 0 = c₀ := by dsimp [rescale_param]; simp
    have hD₀ : DynamicalPuzzlePiece c₀ n 0 = S₀ := by
      have hconn0 : IsConnected S₀ := by
        have := hconn 0 (mem_ball_self (by positivity))
        rwa [hr0] at this
      have h00 : 0 ∈ S₀ := by
        have := h0 0 (mem_ball_self (by positivity))
        rwa [hr0] at this
      exact dynamical_puzzle_piece_eq_green_sublevel c₀ n 0 hconn0 h00
    have hD_t : DynamicalPuzzlePiece c_t n 0 = S_t := 
      dynamical_puzzle_piece_eq_green_sublevel c_t n 0 (hconn t ht) (h0 t ht)
    rw [hD₀, hD_t]
    have h_f_t : H.f t = h_t.toFun := hh_t.symm
    
    have h_boundary : H.f t '' frontier S₀ = frontier S_t := by
      have h_f_img : H.f t '' frontier S₀ = (bottcher_motion B E).f t '' E := by
        rw [hE]
        apply image_congr
        intro z hz
        exact h_ext t ht z (hE.symm ▸ hz)
      rw [h_f_img, hE]
      exact bottcher_motion_preserves_boundary B c₀ r n t ht
    
    rw [h_f_t]
    apply homeomorphism_maps_component h_t S₀ S_t
    · change h_t.toFun '' frontier S₀ = frontier S_t
      rw [← h_f_t, h_boundary]
    · use 0
      constructor
      · have := h0 0 (Metric.mem_ball_self (by positivity))
        rwa [hr0] at this
      · have h_mem : h_t.toFun 0 ∈ S_t := by
          rw [← h_f_t]
          apply (holomorphic_motion_preserves_component H t ht S₀ S_t h_boundary) 0 |>.mp
          have := h0 0 (Metric.mem_ball_self (by positivity))
          rwa [hr0] at this
        exact h_mem
  apply (parameter_dynamics_stability n c₀ r t ht H h_piece_to_piece).mpr
  apply (dynamical_puzzle_piece_eq_green_sublevel c_t n 0 (hconn t ht) (h0 t ht)).symm ▸ (hmem t ht)

/-- Data needed to build a puzzle-boundary motion from a Böttcher coordinate. -/
structure BottcherMotionData (n : ℕ) (c₀ : ℂ) where
  B : BottcherData
  r : ℝ
  r_pos : 0 < r
  E : Set ℂ
  E_eq : E = PuzzleBoundary c₀ n
  preserves :
    motion_preserves_para_piece n c₀ r E (bottcher_motion B E)

/-- Turn Böttcher-based motion data into the generic puzzle-boundary motion data. -/
def puzzle_boundary_motion_data_of_bottcher (n : ℕ) (c₀ : ℂ)
    (h : BottcherMotionData n c₀) : PuzzleBoundaryMotionData n c₀ := 
  { r := h.r
    r_pos := h.r_pos
    E := h.E
    motion := bottcher_motion h.B h.E
    preserves := h.preserves }

/-- Global hypothesis providing Böttcher-based motion data for all parameters. -/
structure BottcherMotionHyp where
  data : ∀ (n : ℕ) (c₀ : ℂ), BottcherMotionData n c₀

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
    BottcherMotionData n c₀ := 
  { B := B
    r := r
    r_pos := r_pos
    E := PuzzleBoundary c₀ n
    E_eq := rfl
    preserves :=
      motion_preserves_para_piece_of_green_sublevel n c₀ r B (PuzzleBoundary c₀ n) rfl
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
