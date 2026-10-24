import Mlc.Literature.Foundations

/-!
# Phase--parameter and puzzle contracts

The classical Douady--Hubbard/Yoccoz route has two distinct layers:

1. external rays, equipotentials, and finite dynamical puzzle graphs;
2. a phase--parameter realization producing connected parapuzzle pieces.

This file records those layers as explicit data.  The final theorem below is
proved from the data, while the existence proposition remains open.
-/

namespace MLC
namespace Literature

open Filter Set Topology

noncomputable section

/-- An external ray with a specified landing point and potential parameter. -/
structure ExternalRaySystem (c : ℂ) where
  ray : ℝ → ℝ → ℂ
  landing : ℝ → ℂ
  ray_continuous : ∀ θ, Continuous (ray θ)
  lands : ∀ θ, Tendsto (ray θ) atTop (𝓝 (landing θ))
  angle_periodic : ∀ θ t, ray (θ + 1) t = ray θ t
  landing_periodic : ∀ θ, landing (θ + 1) = landing θ
  dynamics : ∀ θ t,
    quadraticMap c (ray θ t) = ray (2 * θ) (2 * t)

/-- A finite-level dynamical puzzle graph and its critical pieces. -/
structure DynamicalPuzzleSystem (c : ℂ) where
  rays : ExternalRaySystem c
  graph : ℕ → Set ℂ
  piece : ℕ → Set ℂ
  graph_closed : ∀ n, IsClosed (graph n)
  piece_open : ∀ n, IsOpen (piece n)
  critical_mem : ∀ n, (0 : ℂ) ∈ piece n
  piece_connected : ∀ n, IsConnected (piece n)
  nested : ∀ n, piece (n + 1) ⊆ piece n

/-- A phase--parameter realization of a dynamical puzzle system. -/
structure PhaseParameterPuzzleData
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) where
  dynamical : DynamicalPuzzleSystem c
  parameter_graph : ℕ → Set ℂ
  parameter_piece : ℕ → Set ℂ
  parameter_graph_closed : ∀ n, IsClosed (parameter_graph n)
  parameter_piece_open : ∀ n, IsOpen (parameter_piece n)
  parameter_connected :
    ∀ n, IsConnected (parameter_piece n ∩ reviewMandelbrotSet)
  parameter_contains : ∀ n, c ∈ parameter_piece n
  parameter_basis :
    ∀ U ∈ 𝓝 c, ∃ n, parameter_piece n ⊆ U
  parameter_nested :
    ∀ n, parameter_piece (n + 1) ⊆ parameter_piece n
  parameter_shrinks :
    (⋂ n, parameter_piece n) = {c}
  phase_parameter_compatibility :
    ∀ n, parameter_piece n ⊆
      {z | ∃ w ∈ dynamical.piece n, dist z (w + c) ≤ (1 / 2 : ℝ) ^ n}

/-- Forgetting the analytic source data yields the topological basis used by
the MLC theorem. -/
def PhaseParameterPuzzleData.toParameterPuzzleBasis
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (D : PhaseParameterPuzzleData c hc) :
    ParameterPuzzleBasis c hc where
  piece := D.parameter_piece
  open_piece := D.parameter_piece_open
  connected_piece := D.parameter_connected
  contains_parameter := D.parameter_contains
  basis := D.parameter_basis
  nested := D.parameter_nested
  singleton_intersection := D.parameter_shrinks

theorem localConnectivity_of_phaseParameterData
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (D : PhaseParameterPuzzleData c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  localConnectivity_of_parameterPuzzleBasis
    D.toParameterPuzzleBasis

/-- The exact existence statement left by the graph-cut phase--parameter
theorem.  It is a proposition, not an axiom declaration. -/
def YoccozPhaseParameterResult : Prop :=
  ∀ (c : ℂ) (hc : c ∈ reviewMandelbrotSet),
    Nonempty (PhaseParameterPuzzleData c hc)

end

end Literature
end MLC
