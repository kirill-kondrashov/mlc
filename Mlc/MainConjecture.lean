import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.AxiomsMainConjecture
import Mlc.Quadratic.Complex.BottcherMotion
import Mlc.MandelbrotEquivalence
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Complex.Basic
import Lean

open Lean Elab Command

namespace MLC

open Quadratic Complex Topology Set Filter Bornology Metric

/-!
# Mandelbrot Local Connectivity (MLC) Conjecture

This file outlines the proof strategy for the MLC conjecture based on Yoccoz puzzles.

## Integration with DeepMind Formal Conjectures

The definitions of `multibrotSet` and `mandelbrotSet`, as well as the formulation of the `MLC` theorem
around line 106, are adapted from the Google DeepMind `formal-conjectures` repository:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mandelbrot.lean

Note: Because the `formal-conjectures` repository depends on an older version of Lean/Mathlib (v4.22.0)
which is incompatible with this project's dependencies, we have copied the relevant definitions
and theorem statements here to ensure a valid and consistent formalization.
-/

-- Definitions adapted from DeepMind's FormalConjectures (Wikipedia/Mandelbrot.lean)

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrotSet for n = 2. -/
abbrev mandelbrotSet := multibrotSet 2

-- Equivalence with Yoccoz definition
lemma mandelbrotSet_eq_MandelbrotSet : mandelbrotSet = MLC.Quadratic.MandelbrotSet := by
  exact Mlc.MandelbrotEquivalence.mandelbrot_set_equivalence

section MainProof

/-- Every parameter is either finitely renormalizable (including non-renormalizable) or infinitely renormalizable.
    Proof idea: By the law of excluded middle, the sum of moduli either converges or diverges.
    We use the definition of FinitelyRenormalizable and InfinitelyRenormalizable which directly
    map to this divergence/convergence behavior. -/
theorem dichotomy (c : ℂ) : FinitelyRenormalizable c ∨ InfinitelyRenormalizable c := by
  unfold FinitelyRenormalizable InfinitelyRenormalizable
  rw [or_comm]
  exact Classical.em _

/-- If parameter pieces shrink to a point, they form a neighborhood basis at `c`. -/
lemma parameter_shrink_basis (c : ℂ) (h : (⋂ n, ParaPuzzlePiece n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePiece n ⊆ U := by
  exact MLC.Quadratic.parameter_shrink c h

/-- The core strategy theorem (internal). -/
theorem mlc_strategy
    (h_param_shrink :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        (⋂ n, MLC.Quadratic.ParaPuzzlePiece n) = {c})
    (h_bottcher_onM : MLC.Quadratic.BottcherOnMHyp)
    (h_green_conn : MLC.Quadratic.GreenSublevelConnectedHyp)
    (h_classify : ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c)
    (h_bridge :
      MoleculeConjectureRefined →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin_renorm | h_inf_renorm
  · -- Case 1: Finitely Renormalizable
    have h_motion : MLC.Quadratic.PuzzleBoundaryMotionHyp :=
      MLC.Quadratic.puzzle_boundary_motion_hyp_of_onM_connected
        (MLC.Quadratic.bottcher_green_sublevel_hyp_onM_connected_of_onM h_bottcher_onM h_green_conn)
    exact mlc_finitely_renormalizable c hc h_motion h_fin_renorm (h_param_shrink c hc h_fin_renorm)
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable h_classify h_bridge c hc h_inf_renorm

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/
theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  apply mlc_strategy
  · -- Finitely Renormalizable case (Yoccoz)
    intro c hc h_fin
    exact yoccoz_parameter_shrink c hc h_fin
  · -- Bottcher coordinates exist on M
    exact bottcher_onM_hyp
  · -- Green sublevel sets connected
    exact green_sublevel_connected_hyp
  · -- Classification of infinitely renormalizable parameters (Lyubich)
    intro c h_inf
    exact classify_infinitely_renormalizable c h_inf
  · -- Bridge from Molecule Conjecture to Satellite MLC
    intro h_mol c hc h_sat
    exact molecule_conjecture_bridge h_mol c hc h_sat

end MainProof

end MLC
