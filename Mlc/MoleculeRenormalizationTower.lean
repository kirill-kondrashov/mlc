import Molecule.Rfast

namespace MLC

open Molecule

noncomputable section

/-! The minimal tower interface needed for the satellite branch. -/
structure RenormalizationTower (g : BMol) where
  gₙ : ℕ → BMol
  g0 : gₙ 0 = g
  step : ∀ n : ℕ, Nonempty (RenormalizationRelation (gₙ n) (gₙ (n + 1)))

namespace RenormalizationTower

noncomputable def rel {g : BMol} (T : RenormalizationTower g) (n : ℕ) :
    RenormalizationRelation (T.gₙ n) (T.gₙ (n + 1)) :=
  Classical.choice (T.step n)

noncomputable def period {g : BMol} (T : RenormalizationTower g) (n : ℕ) : ℕ :=
  (T.rel n).p

noncomputable def cumulativePeriod {g : BMol} (T : RenormalizationTower g) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cumulativePeriod T n + T.period n

theorem cumulativePeriod_monotone {g : BMol} (T : RenormalizationTower g) :
    Monotone T.cumulativePeriod := by
  intro a b hab
  refine Nat.le_induction (m := a) (n := b) ?_ ?_ hab
  · rfl
  · intro k _hk ih
    simpa [RenormalizationTower.cumulativePeriod] using
      le_trans ih (Nat.le_add_right _ _)

end RenormalizationTower

end

end MLC
