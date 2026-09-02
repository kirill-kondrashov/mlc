import Mlc.Quadratic.Complex.ParaPuzzle

namespace MLC

namespace Quadratic

open Complex Set

noncomputable section

namespace PrincipalNest

/-! Dynamical shrinkage transfers to the translated parameter pieces. -/
theorem para_iInter_eq_singleton_of_dyn_iInter_eq_singleton
    (c : ℂ) (h_dyn : (⋂ n, DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, ParaPuzzlePieceAt c n) = {c} := by
  let f : ℂ → ℂ := fun z => z + c
  have hf : Function.Bijective f := (Homeomorph.addRight c).bijective
  have h_piece (n : ℕ) :
      ParaPuzzlePieceAt c n = f '' DynamicalPuzzlePiece c n 0 := by
    ext z
    constructor
    · intro hz
      exact ⟨z - c, (mem_paraPuzzlePieceAt_iff c z n).mp hz, by
        dsimp [f]
        ring⟩
    · rintro ⟨w, hw, rfl⟩
      exact (mem_paraPuzzlePieceAt_iff c (w + c) n).2 (by simpa)
  rw [show (⋂ n, ParaPuzzlePieceAt c n) =
      ⋂ n, f '' DynamicalPuzzlePiece c n 0 by
    simp_rw [h_piece]]
  rw [← Set.image_iInter hf, h_dyn]
  simp [f]

end PrincipalNest

end

end Quadratic

end MLC
