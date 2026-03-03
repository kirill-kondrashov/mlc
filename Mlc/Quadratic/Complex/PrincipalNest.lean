import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mlc.Quadratic.Complex.ParaPuzzle

namespace MLC.Quadratic

open Complex Set

noncomputable section

/-!
Principal nests (DLS17-style) are typically defined as a cofinal subsequence of Yoccoz puzzle pieces
selected by renormalization combinatorics ("favorite children"/first return maps).

This file sets up the *abstract* interface we will need:
given a cofinal sequence of depths, define the associated dynamical/parameter nests and prove
that intersecting along a cofinal subsequence is equivalent to intersecting along all depths.

The hard part (still missing) is to construct such a cofinal sequence for satellite
renormalizable parameters and prove uniform modulus bounds for the associated annuli.
-/

namespace PrincipalNest

/-- A depth selection is *cofinal* if it eventually exceeds every natural number. -/
def Cofinal (depths : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ depths n

theorem iInter_of_antitone_of_cofinal {α : Type*} (P : ℕ → Set α) (depths : ℕ → ℕ)
    (hP : Antitone P) (hcof : Cofinal depths) :
    (⋂ n, P (depths n)) = ⋂ n, P n := by
  ext x
  constructor
  · intro hx
    refine mem_iInter.mpr ?_
    intro N
    rcases hcof N with ⟨n, hn⟩
    have hx' : x ∈ P (depths n) := mem_iInter.mp hx n
    -- `hP` is `a ≤ b -> P b ⊆ P a`.
    exact (hP hn) hx'
  · intro hx
    refine mem_iInter.mpr ?_
    intro n
    exact mem_iInter.mp hx (depths n)

theorem antitone_dynamicalPuzzlePiece (c : ℂ) :
    Antitone (fun n : ℕ => DynamicalPuzzlePiece c n 0) := by
  intro a b hab
  -- `dynamical_puzzle_piece_nested` gives one-step nesting; iterate it.
  have hbase :
      DynamicalPuzzlePiece c a 0 ⊆ DynamicalPuzzlePiece c a 0 := subset_rfl
  have hstep :
      ∀ k, a ≤ k →
        DynamicalPuzzlePiece c k 0 ⊆ DynamicalPuzzlePiece c a 0 →
          DynamicalPuzzlePiece c (k + 1) 0 ⊆ DynamicalPuzzlePiece c a 0 := by
    intro k _hk hk
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (dynamical_puzzle_piece_nested c k).trans hk
  exact Nat.le_induction hbase hstep b hab

axiom antitone_paraPuzzlePieceAt (c : ℂ) :
    Antitone (fun n : ℕ => ParaPuzzlePieceAt c n)

/-- The dynamical principal nest determined by a depth selection. -/
def dyn (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) : Set ℂ :=
  DynamicalPuzzlePiece c (depths n) 0

/-- The parameter principal nest determined by a depth selection. -/
def para (c : ℂ) (depths : ℕ → ℕ) (n : ℕ) : Set ℂ :=
  ParaPuzzlePieceAt c (depths n)

theorem iInter_dyn_eq (c : ℂ) (depths : ℕ → ℕ) (hcof : Cofinal depths) :
    (⋂ n, dyn c depths n) = ⋂ n, DynamicalPuzzlePiece c n 0 := by
  simpa [dyn] using
    iInter_of_antitone_of_cofinal (P := fun n => DynamicalPuzzlePiece c n 0) depths
      (antitone_dynamicalPuzzlePiece c) hcof

theorem iInter_para_eq (c : ℂ) (depths : ℕ → ℕ) (hcof : Cofinal depths) :
    (⋂ n, para c depths n) = ⋂ n, ParaPuzzlePieceAt c n := by
  simpa [para] using
    iInter_of_antitone_of_cofinal (P := fun n => ParaPuzzlePieceAt c n) depths
      (antitone_paraPuzzlePieceAt c) hcof

end PrincipalNest

end

end MLC.Quadratic
