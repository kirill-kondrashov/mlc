import Yoccoz.Quadratic.Complex.Puzzle

namespace MLC.Quadratic

open Set

/-!
Parameterized para-puzzle pieces centered at a base parameter `c`.

We model the parameter piece of depth `n` at `c` as the translate of the
dynamical puzzle piece around the critical point.
-/

/-- Parameter puzzle piece of depth `n` centered at `c`. -/
def ParaPuzzlePieceAt (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}

lemma mem_paraPuzzlePieceAt_iff (c c' : ℂ) (n : ℕ) :
    c' ∈ ParaPuzzlePieceAt c n ↔ c' - c ∈ DynamicalPuzzlePiece c n 0 := by
  rfl

end MLC.Quadratic
