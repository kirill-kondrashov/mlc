import Yoccoz.Quadratic.Complex.Puzzle

namespace MLC.Quadratic

open Set

/-!
Parameterized para-puzzle pieces centered at a base parameter `c`.

We model the parameter piece of depth `n` at `c` as the translate of the
dynamical puzzle piece around the critical point.
-/

/-- Simplified frozen parameter piece of depth `n` centered at `c`.

    This is a translate of a full dynamical Green sublevel component. It is
    useful for the checked reduction, but it is not the graph-cut
    parapuzzle piece used in the classical Yoccoz construction. -/
def ParaPuzzlePieceAt (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}

lemma mem_paraPuzzlePieceAt_iff (c c' : ℂ) (n : ℕ) :
    c' ∈ ParaPuzzlePieceAt c n ↔ c' - c ∈ DynamicalPuzzlePiece c n 0 := by
  rfl

end MLC.Quadratic
