import Mlc.Quadratic.Complex.ParaPuzzleBasis

namespace MLC.Quadratic

open Complex Topology Set

noncomputable section

/-- Parameter puzzle pieces are open sets. -/
theorem para_puzzle_piece_open (c : ℂ) (n : ℕ) :
    IsOpen (ParaPuzzlePieceAt c n) :=
  para_puzzle_piece_at_isOpen c n

/-- Parameter puzzle pieces form a basis of neighborhoods if they shrink to a
point. -/
theorem para_puzzle_piece_basis (c : ℂ)
    (h : (⋂ n, ParaPuzzlePieceAt c n) = {c}) :
    ∀ U ∈ 𝓝 c, ∃ n, ParaPuzzlePieceAt c n ⊆ U :=
  para_puzzle_piece_basis_sketch c h

end

end MLC.Quadratic
