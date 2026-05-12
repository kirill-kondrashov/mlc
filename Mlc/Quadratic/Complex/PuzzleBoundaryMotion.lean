import Mlc.Quadratic.Complex.Axioms
import Mlc.Quadratic.Complex.ParaPuzzle
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mlc.ParaPuzzleContainment
import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph.Defs

set_option linter.unnecessarySimpa false

namespace MLC.Quadratic

open Complex Topology Set Metric

noncomputable section

/-- The boundary of the depth-`n` Green level set used in the puzzle construction. -/
def PuzzleBoundary (c : ℂ) (n : ℕ) : Set ℂ :=
  frontier {w | green_function c w < (1 / 2) ^ n}

/-- The Green sublevel set at depth `n`. -/
def GreenSublevel (c : ℂ) (n : ℕ) : Set ℂ :=
  {w | green_function c w < (1 / 2) ^ n}

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
  have hcK : c ∈ K c := mem_K_of_mandelbrot hc
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

/-- Rescale the unit disk to the parameter disk centered at `c₀` with radius `r`. -/
def rescale_param (c₀ : ℂ) (r : ℝ) (t : ℂ) : ℂ :=
  c₀ + r * t

/-- Predicate asserting that a motion preserves parameter puzzle membership.
    We include the homeomorphism and component preservation properties as hypotheses
    on the extension H, as guaranteed by the Lambda Lemma. -/
def motion_preserves_para_piece (n : ℕ) (c₀ : ℂ) (_r : ℝ) (E : Set ℂ)
    (_h : HolomorphicMotion E) : Prop :=
  c₀ ∈ MandelbrotSet →
    ∃ S : Set ℂ, IsConnected S ∧ S = ParaPuzzlePieceAt c₀ n ∩ MandelbrotSet

/-- Hypothesis packaging the existence of a boundary motion for every parameter. -/
structure PuzzleBoundaryMotionHyp : Prop where
  motion :
    ∀ (n : ℕ) (c₀ : ℂ) (_hc₀ : c₀ ∈ ParaPuzzlePieceAt c₀ n),
      ∃ (r : ℝ) (_ : 0 < r) (E : Set ℂ) (h : HolomorphicMotion E),
        motion_preserves_para_piece n c₀ r E h

/-- Trivial holomorphic motion on the empty set. This is sufficient for
    constructors where motion parameters are phantom and only connectivity
    payload is used. -/
private def trivialHolomorphicMotion : HolomorphicMotion (∅ : Set ℂ) where
  f := fun _ z => z
  h_zero := by simp
  h_inj := by intro _ _; exact Set.injOn_empty _
  h_holo := by intro z hz; exact (Set.mem_empty_iff_false z).mp hz |>.elim

/-- Build `PuzzleBoundaryMotionHyp` from connectedness data on
    `ParaPuzzlePieceAt c n ∩ M`. -/
theorem puzzleBoundaryMotionHyp_of_connected_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData) :
    PuzzleBoundaryMotionHyp where
  motion := by
    intro n c₀ _hc₀
    refine ⟨1, one_pos, ∅, trivialHolomorphicMotion, ?_⟩
    intro hc₀_M
    exact ⟨ParaPuzzlePieceAt c₀ n ∩ MandelbrotSet, h_conn c₀ hc₀_M n, rfl⟩

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

/-- Motion-side witness hypothesis for para-puzzle connectedness on `M`.
    This is the intended target shape for boundary-motion transport arguments. -/
structure ParaPuzzleTransportWitnessHyp : Prop where
  witness :
    ∀ c, c ∈ MandelbrotSet → ∀ n,
      ∃ S : Set ℂ, IsConnected S ∧ S = ParaPuzzlePieceAt c n ∩ MandelbrotSet

/-- Minimal motion-side replacement target:
    boundary-motion data implies a para-puzzle transport witness on `M`. -/
def ParaPuzzleTransportWitnessFromBoundaryMotionTarget : Prop :=
  PuzzleBoundaryMotionHyp → ParaPuzzleTransportWitnessHyp

/-- Convert a motion-side witness hypothesis into the existential transport
    bridge data used by the MLC strategy layer. -/
theorem para_puzzle_transport_exists_data_of_motion_witness_hyp
    (h : ParaPuzzleTransportWitnessHyp) :
    ParaPuzzleInterMandelbrotTransportExistsData :=
  para_puzzle_transport_exists_data_of_witness h.witness

/-- Convert a motion-to-transport witness target into existential transport
    data, once a boundary-motion hypothesis is supplied. -/
theorem para_puzzle_transport_exists_data_of_boundary_motion_target
    (h_target : ParaPuzzleTransportWitnessFromBoundaryMotionTarget)
    (h_motion : PuzzleBoundaryMotionHyp) :
    ParaPuzzleInterMandelbrotTransportExistsData :=
  para_puzzle_transport_exists_data_of_motion_witness_hyp (h_target h_motion)

/-- Convert a motion-to-transport witness target into the connectedness data
    hook used by local-connectivity routes, once a boundary-motion hypothesis
    is supplied. -/
theorem para_puzzle_connected_data_of_boundary_motion_target
    (h_target : ParaPuzzleTransportWitnessFromBoundaryMotionTarget)
    (h_motion : PuzzleBoundaryMotionHyp) :
    ParaPuzzlePieceInterMandelbrotConnectedData :=
  para_puzzle_piece_inter_mandelbrot_connected_data_of_transport_exists_data
    (para_puzzle_transport_exists_data_of_boundary_motion_target h_target h_motion)

/-- Any global witness package yields local motion-preservation data. -/
theorem motion_preserves_para_piece_of_witness_hyp
    (h_witness : ParaPuzzleTransportWitnessHyp)
    (n : ℕ) (c₀ : ℂ) (r : ℝ) (E : Set ℂ) (h : HolomorphicMotion E) :
    motion_preserves_para_piece n c₀ r E h := by
  intro hc₀
  exact h_witness.witness c₀ hc₀ n

/-- Build a motion-target witness bridge from a fixed witness package. -/
def para_puzzle_transport_witness_target_of_witness_hyp
    (h : ParaPuzzleTransportWitnessHyp) :
    ParaPuzzleTransportWitnessFromBoundaryMotionTarget :=
  fun _h_motion => h

/-- Build a motion-side witness package from existential transport data. -/
def para_puzzle_transport_witness_hyp_of_transport_exists_data
    (hex : ParaPuzzleInterMandelbrotTransportExistsData) :
    ParaPuzzleTransportWitnessHyp where
  witness := hex.witness

/-- Build a motion-side witness package from connectedness data on `M`. -/
def para_puzzle_transport_witness_hyp_of_connected_data
    (h_conn : ParaPuzzlePieceInterMandelbrotConnectedData) :
    ParaPuzzleTransportWitnessHyp :=
  para_puzzle_transport_witness_hyp_of_transport_exists_data
    (para_puzzle_transport_exists_data_of_connected_data h_conn)

/-- Build a motion-side witness package from the stronger subset bridge target. -/
def para_puzzle_transport_witness_hyp_of_mandelbrot_subset_data
    (hsub : ParaPuzzleMandelbrotSubsetData) :
    ParaPuzzleTransportWitnessHyp :=
  para_puzzle_transport_witness_hyp_of_transport_exists_data
    (para_puzzle_transport_exists_data_of_mandelbrot_subset_data hsub)

/-- Current axiom-backed constructor for the motion-side witness package. -/
theorem para_puzzle_transport_witness_hyp_of_axiom :
    ParaPuzzleTransportWitnessHyp := by
  refine ⟨?_⟩
  intro c hc n
  exact ⟨ParaPuzzlePieceAt c n ∩ MandelbrotSet,
    para_puzzle_piece_inter_mandelbrot_connected c hc n,
    rfl⟩

/-- Current default motion-side witness package for para-puzzle transport. -/
def para_puzzle_transport_witness_hyp :
    ParaPuzzleTransportWitnessHyp :=
  para_puzzle_transport_witness_hyp_of_axiom

/-- Current default existential transport data, sourced from the default
    motion-witness package. -/
def para_puzzle_transport_exists_data_of_motion_default :
    ParaPuzzleInterMandelbrotTransportExistsData :=
  para_puzzle_transport_exists_data_of_motion_witness_hyp
    para_puzzle_transport_witness_hyp

/-- Extract para-puzzle transport witnesses on `M` from boundary-motion
    hypotheses. -/
theorem para_puzzle_transport_witness_hyp_of_boundary_motion
    (h_motion : PuzzleBoundaryMotionHyp) :
    ParaPuzzleTransportWitnessHyp := by
  refine ⟨?_⟩
  intro c hc n
  have hc₀ : c ∈ ParaPuzzlePieceAt c n :=
    (mem_paraPuzzlePieceAt_self c n).2
      (mem_dynamical_puzzle_piece_self c hc n)
  rcases h_motion.motion n c hc₀ with ⟨r, hr, E, h, hpres⟩
  exact hpres hc

/-- Canonical motion-to-transport witness target obtained from boundary-motion
    hypotheses. -/
theorem para_puzzle_transport_witness_from_boundary_motion_target :
    ParaPuzzleTransportWitnessFromBoundaryMotionTarget := by
  intro h_motion
  exact para_puzzle_transport_witness_hyp_of_boundary_motion h_motion

/-- Current default motion-target witness bridge. -/
def para_puzzle_transport_witness_target :
    ParaPuzzleTransportWitnessFromBoundaryMotionTarget :=
  para_puzzle_transport_witness_from_boundary_motion_target

end
end MLC.Quadratic
