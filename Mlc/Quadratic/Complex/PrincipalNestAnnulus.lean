import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Yoccoz.Quadratic.Complex.Groetzsch
import Mlc.Quadratic.Complex.PrincipalNest
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

/-- The para principal annulus between successive parameter nest pieces. -/
def paraAnnulus (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) : Set ℂ :=
  ParaPuzzlePieceAt c (depths n) \ ParaPuzzlePieceAt c (depths (n + 1))

@[simp] lemma dynAnnulus_id (c : ℂ) (n : ℕ) :
    dynAnnulus c (fun k => k) n = PuzzleAnnulus c n := by
  simp [dynAnnulus, PuzzleAnnulus]

lemma dynAnnulus_subset_left (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) :
    dynAnnulus c depths n ⊆ DynamicalPuzzlePiece c (depths n) 0 := by
  intro z hz
  exact hz.1

lemma paraAnnulus_subset_left (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) :
    paraAnnulus c depths n ⊆ ParaPuzzlePieceAt c (depths n) := by
  intro z hz
  exact hz.1

lemma dynAnnulus_disjoint_right (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) :
    Disjoint (dynAnnulus c depths n) (DynamicalPuzzlePiece c (depths (n + 1)) 0) := by
  refine disjoint_left.2 ?_
  intro z hz1 hz2
  exact hz1.2 hz2

lemma paraAnnulus_disjoint_right (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) :
    Disjoint (paraAnnulus c depths n) (ParaPuzzlePieceAt c (depths (n + 1))) := by
  refine disjoint_left.2 ?_
  intro z hz1 hz2
  exact hz1.2 hz2

end PrincipalNest

end

end MLC.Quadratic
