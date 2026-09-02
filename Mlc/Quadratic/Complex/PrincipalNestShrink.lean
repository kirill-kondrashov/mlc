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
  ext z
  constructor
  · intro hz
    have hz_dyn : z - c ∈ ⋂ n, DynamicalPuzzlePiece c n 0 := by
      refine Set.mem_iInter.mpr ?_
      intro n
      exact (mem_paraPuzzlePieceAt_iff c z n).mp (Set.mem_iInter.mp hz n)
    have hz_zero : z - c = 0 := by
      have : z - c ∈ ({0} : Set ℂ) := by simpa [h_dyn] using hz_dyn
      simpa using this
    simpa using sub_eq_zero.mp hz_zero
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    refine Set.mem_iInter.mpr ?_
    intro n
    have h0_all : 0 ∈ ⋂ k, DynamicalPuzzlePiece c k 0 := by
      have : 0 ∈ ({0} : Set ℂ) := by simp
      simpa [h_dyn] using this
    exact (mem_paraPuzzlePieceAt_iff c c n).2
      (by simpa using Set.mem_iInter.mp h0_all n)

end PrincipalNest

end

end Quadratic

end MLC
