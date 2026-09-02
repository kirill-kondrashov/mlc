import Mlc.Quadratic.Complex.ParaPuzzle

namespace MLC.Quadratic

open Complex Set

noncomputable section

/-!
Principal nest annuli.

In the DLS17 principal nest, one selects a cofinal sequence of puzzle depths (often via
"favorite children"/first return maps) and studies the moduli of the annuli between successive
nest elements. This file defines the generic annulus between two selected depths, and proves
basic bookkeeping lemmas.

This file intentionally does *not* attempt to build the DLS selection or prove a priori bounds.
-/

namespace PrincipalNest

/-- The dynamical principal annulus between successive nest pieces. -/
def dynAnnulus (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c (depths n) 0 \ DynamicalPuzzlePiece c (depths (n + 1)) 0

end PrincipalNest

end

end MLC.Quadratic
