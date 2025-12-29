import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green
import Mathlib.Topology.Connected.Basic

/-!
# Yoccoz Puzzles

This file defines the Yoccoz puzzle pieces for the quadratic family f_c(z) = z^2 + c.

## Definitions

* `puzzle_set c n`: The set K(c) ∪ {z | G_c(z) < 1/2^n}.
* `DynamicalPuzzlePiece c n z`: The connected component of `puzzle_set c n` containing `z`.

## References

* "Conformal Geometry and Dynamics of Quadratic Polynomials", Section 21.
-/

namespace MLC.Quadratic

open Complex Topology Filter Set

noncomputable section

variable (c : ℂ)

/-- The set defining the level n puzzle pieces: K(c) ∪ {z | G_c(z) < 1/2^n}. -/
def puzzle_set (n : ℕ) : Set ℂ :=
  K c ∪ {z | green_function c z < (1 / 2 : ℝ) ^ n}

/-- The dynamical puzzle piece of depth n containing z.
    Defined as the connected component of `puzzle_set c n` containing `z`. -/
def DynamicalPuzzlePiece (n : ℕ) (z : ℂ) : Set ℂ :=
  connectedComponentIn (puzzle_set c n) z

end

end MLC.Quadratic
