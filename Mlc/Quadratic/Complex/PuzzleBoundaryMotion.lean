import Mlc.Quadratic.Complex.Axioms
import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Basic

set_option linter.unnecessarySimpa false

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-- The boundary of the depth-`n` Green level set used in the puzzle construction. -/
def PuzzleBoundary (c : ℂ) (n : ℕ) : Set ℂ :=
  frontier {w | green_function c w < (1 / 2) ^ n}

/-- The Green sublevel set at depth `n`. -/
def GreenSublevel (c : ℂ) (n : ℕ) : Set ℂ :=
  {w | green_function c w < (1 / 2) ^ n}

/-- If `c` is in the Mandelbrot set, then `c ∈ K(c)`. -/
theorem mem_K_of_mandelbrot (c : ℂ) (hc : c ∈ MandelbrotSet) : c ∈ K c := by
  unfold K MandelbrotSet boundedOrbit at *
  obtain ⟨M, hM⟩ := hc
  refine ⟨max M ‖c‖, ?_⟩
  intro n
  have h_shift : ∀ k, orbit c c k = orbit c 0 (k + 1) := by
    intro k
    induction k with
    | zero => simp [orbit, fc]
    | succ k ih => simp [orbit_succ, ih]
  have h_bound : ‖orbit c c n‖ ≤ M := by
    have hM' : ‖orbit c 0 (n + 1)‖ ≤ M := hM (n + 1)
    simpa [h_shift n] using hM'
  exact le_trans h_bound (le_max_left _ _)

/-- If `c ∈ M`, then `0` lies in the Green sublevel set. -/
theorem green_sublevel_contains_0 (c : ℂ) (n : ℕ) (hc : c ∈ MandelbrotSet) :
    0 ∈ GreenSublevel c n := by
  have h0K : 0 ∈ K c := hc
  have h0 : green_function c 0 = 0 :=
    (green_function_eq_zero_iff_mem_K c 0).2 h0K
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by
    exact pow_pos (by norm_num) _
  have : green_function c 0 < (1 / 2 : ℝ) ^ n := by
    simpa [h0] using hpos
  exact this

/-- If `c ∈ M`, then `c` lies in the Green sublevel set. -/
theorem green_sublevel_contains_c (c : ℂ) (n : ℕ) (hc : c ∈ MandelbrotSet) :
    c ∈ GreenSublevel c n := by
  have hcK : c ∈ K c := mem_K_of_mandelbrot c hc
  have hc0 : green_function c c = 0 :=
    (green_function_eq_zero_iff_mem_K c c).2 hcK
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by
    exact pow_pos (by norm_num) _
  have : green_function c c < (1 / 2 : ℝ) ^ n := by
    simpa [hc0] using hpos
  exact this

/-- Hypothesis: Green sublevels are connected on the Mandelbrot set. -/
structure GreenSublevelConnectedHyp : Prop where
  connected : ∀ (c : ℂ) (n : ℕ), c ∈ MandelbrotSet → IsConnected (GreenSublevel c n)

/-- If the Green sublevel set is connected and contains both `0` and `c`,
    then `c` lies in the corresponding parameter puzzle piece. -/
theorem para_puzzle_piece_of_sublevel_connected (c : ℂ) (n : ℕ)
    (h0 : 0 ∈ GreenSublevel c n)
    (hc : c ∈ GreenSublevel c n)
    (hconn : IsConnected (GreenSublevel c n)) :
    c ∈ ParaPuzzlePiece n := by
  have hsubset : GreenSublevel c n ⊆ connectedComponentIn (GreenSublevel c n) 0 := by
    exact hconn.isPreconnected.subset_connectedComponentIn h0 (by
      intro x hx
      exact hx)
  have hc_in : c ∈ connectedComponentIn (GreenSublevel c n) 0 := hsubset hc
  -- Avoid `simpa` here to keep the linter quiet.
  exact (by
    simpa [ParaPuzzlePiece, DynamicalPuzzlePiece, GreenSublevel] using hc_in)

/-- Rescale the unit disk to the parameter disk centered at `c₀` with radius `r`. -/
def rescale_param (c₀ : ℂ) (r : ℝ) (t : ℂ) : ℂ :=
  c₀ + r * t

/-- Predicate asserting that a motion preserves parameter puzzle membership. -/
def motion_preserves_para_piece (n : ℕ) (c₀ : ℂ) (r : ℝ) (E : Set ℂ)
    (h : HolomorphicMotion E) : Prop :=
  ∀ (H : HolomorphicMotion Set.univ),
    (∀ t ∈ Metric.ball 0 1, ∀ z ∈ E, H.f t z = h.f t z) →
    ∀ t ∈ Metric.ball 0 1, rescale_param c₀ r t ∈ ParaPuzzlePiece n

/-- Hypothesis packaging the existence of a boundary motion for every parameter. -/
structure PuzzleBoundaryMotionHyp : Prop where
  motion :
    ∀ (n : ℕ) (c₀ : ℂ) (_hc₀ : c₀ ∈ ParaPuzzlePiece n),
      ∃ (r : ℝ) (_ : 0 < r) (E : Set ℂ) (h : HolomorphicMotion E),
        motion_preserves_para_piece n c₀ r E h

/-- The identity holomorphic motion on any set. -/
def identity_motion (E : Set ℂ) : HolomorphicMotion E :=
  { f := fun _ z => z
    h_zero := by intro z hz; rfl
    h_inj := by
      intro t ht x hx y hy hxy
      simpa using hxy
    h_holo := by
      intro z hz
      simpa using (differentiableOn_const : DifferentiableOn ℂ (fun _ : ℂ => z) (Metric.ball 0 1)) }

/-- Existence of a holomorphic motion on any set (trivial identity motion). -/
theorem exists_holomorphic_motion (E : Set ℂ) : Nonempty (HolomorphicMotion E) := by
  exact ⟨identity_motion E⟩

/-- A holomorphic motion on the puzzle boundary (trivial identity motion). -/
theorem puzzle_boundary_motion_trivial (c : ℂ) (n : ℕ) :
    Nonempty (HolomorphicMotion (PuzzleBoundary c n)) := by
  exact exists_holomorphic_motion (PuzzleBoundary c n)

/-- Assemble the data needed for a parameter-stability motion. -/
structure PuzzleBoundaryMotionData (n : ℕ) (c₀ : ℂ) where
  r : ℝ
  r_pos : 0 < r
  E : Set ℂ
  motion : HolomorphicMotion E
  preserves : motion_preserves_para_piece n c₀ r E motion

/-- If the motion data is provided, we can package it in the form used elsewhere. -/
theorem puzzle_boundary_motion_exists_of_data (n : ℕ) (c₀ : ℂ)
    (h : PuzzleBoundaryMotionData n c₀) :
    ∃ (r : ℝ) (_ : 0 < r) (E : Set ℂ) (h : HolomorphicMotion E),
      motion_preserves_para_piece n c₀ r E h := by
  refine ⟨h.r, h.r_pos, h.E, h.motion, h.preserves⟩

end
end MLC.Quadratic
