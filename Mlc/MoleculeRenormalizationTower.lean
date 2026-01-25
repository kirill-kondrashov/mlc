import Molecule.Rfast
import Mlc.Quadratic.Complex.PrincipalNest

namespace MLC

open Molecule

noncomputable section

/-!
This file packages the purely *combinatorial* consequences of having an infinite tower of
renormalizations in the Molecule framework.

It does **not** connect to Yoccoz puzzle geometry yet; the purpose is to have a clean place
to build the eventual dictionary:

  satellite renormalization tower (BMol) -> cofinal "principal nest" index sequence.
-/

structure RenormalizationTower (g : BMol) where
  /-- The n-th renormalization level map. -/
  gₙ : ℕ → BMol
  g0 : gₙ 0 = g
  /-- Each level renormalizes to the next. -/
  step : ∀ n : ℕ, Nonempty (RenormalizationRelation (gₙ n) (gₙ (n + 1)))

namespace RenormalizationTower

noncomputable def rel {g : BMol} (T : RenormalizationTower g) (n : ℕ) :
    RenormalizationRelation (T.gₙ n) (T.gₙ (n + 1)) :=
  Classical.choice (T.step n)

noncomputable def period {g : BMol} (T : RenormalizationTower g) (n : ℕ) : ℕ :=
  (T.rel n).p

theorem period_ge_two {g : BMol} (T : RenormalizationTower g) (n : ℕ) : 2 ≤ T.period n :=
  (T.rel n).p_pos

noncomputable def cumulativePeriod {g : BMol} (T : RenormalizationTower g) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cumulativePeriod T n + T.period n

theorem cumulativePeriod_monotone {g : BMol} (T : RenormalizationTower g) :
    Monotone T.cumulativePeriod := by
  intro a b hab
  -- Induct from `a` up to `b`.
  refine Nat.le_induction (m := a) (n := b) ?base ?step hab
  · rfl
  · intro k _hk ih
    -- `cumulativePeriod (k+1) = cumulativePeriod k + period k ≥ cumulativePeriod k`.
    simpa [RenormalizationTower.cumulativePeriod] using
      le_trans ih (Nat.le_add_right _ _)

theorem le_cumulativePeriod_of_le {g : BMol} (T : RenormalizationTower g) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ T.cumulativePeriod n := by
  intro N
  refine ⟨N, ?_⟩
  -- The cumulative sum grows at least linearly since each period is >= 2.
  -- In particular, `cumulativePeriod n ≥ n`.
  have hlin : ∀ n : ℕ, n ≤ T.cumulativePeriod n := by
    intro n
    induction n with
    | zero => simp [cumulativePeriod]
    | succ n ih =>
        have hper : 1 ≤ T.period n := le_trans (by decide : (1 : ℕ) ≤ 2) (T.period_ge_two n)
        simpa [cumulativePeriod, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          add_le_add ih hper
  exact le_trans (le_of_eq rfl) (hlin N)

theorem cumulativePeriod_cofinal {g : BMol} (T : RenormalizationTower g) :
    MLC.Quadratic.PrincipalNest.Cofinal T.cumulativePeriod :=
  le_cumulativePeriod_of_le T

end RenormalizationTower

end

end MLC
