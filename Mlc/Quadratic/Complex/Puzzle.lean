import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Groetzsch
import Mlc.Quadratic.Complex.Green
import Mlc.CheckAxioms
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- The dynamical puzzle piece of depth n containing z. -/
def DynamicalPuzzlePiece (c : ℂ) (n : ℕ) (z : ℂ) : Set ℂ :=
  connectedComponentIn {w | green_function c w < (1 / 2) ^ n} z

/-- The annulus between two nested puzzle pieces around the critical point. -/
def PuzzleAnnulus (c : ℂ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c n 0 \ DynamicalPuzzlePiece c (n + 1) 0

/-- A para-puzzle piece in the parameter plane. -/
def ParaPuzzlePiece (n : ℕ) : Set ℂ := {c | c ∈ DynamicalPuzzlePiece c n 0}

end

end MLC.Quadratic
