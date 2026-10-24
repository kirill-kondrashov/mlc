import Mlc.Literature.Dudko
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Renormalization combinatorics and modulus arithmetic

This module formalizes the discrete part of the renormalization contracts:
primitive/satellite/neutral labels, bounded type, period-doubling profiles,
cumulative depths, and the elementary divergence consequence of a uniform
modulus lower bound.
-/

namespace MLC
namespace Literature

open Filter

noncomputable section

/-- A natural-valued sequence is of bounded type if it has a global bound. -/
def BoundedType (a : ℕ → ℕ) : Prop :=
  ∃ B, ∀ n, a n ≤ B

/-- The discrete combinatorics recorded at each renormalization level. -/
structure RenormalizationCombinatorics where
  kind : RenormalizationClass
  period : ℕ → ℕ
  period_pos : ∀ n, 0 < period n
  rotation : ℕ → ℕ

def IsPrimitiveProfile (R : RenormalizationCombinatorics) : Prop :=
  R.kind = .primitive

def IsSatelliteProfile (R : RenormalizationCombinatorics) : Prop :=
  R.kind = .satellite

def IsNeutralProfile (R : RenormalizationCombinatorics) : Prop :=
  R.kind = .neutral

def IsBoundedTypeSatelliteProfile (R : RenormalizationCombinatorics) : Prop :=
  IsSatelliteProfile R ∧ BoundedType R.rotation

def IsPeriodDoublingProfile (R : RenormalizationCombinatorics) : Prop :=
  IsPrimitiveProfile R ∧ ∀ n, R.period n = 2

def IsBoundedPeriodDoublingProfile
    (R : RenormalizationCombinatorics) : Prop :=
  IsPeriodDoublingProfile R ∧ BoundedType R.rotation

/-- Cumulative return depth of a discrete renormalization profile. -/
def cumulativeDepth (R : RenormalizationCombinatorics) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cumulativeDepth R n + R.period n

theorem cumulativeDepth_monotone
    (R : RenormalizationCombinatorics) :
    Monotone (cumulativeDepth R) := by
  intro a b hab
  refine Nat.le_induction (m := a) (n := b) ?_ ?_ hab
  · rfl
  · intro k _hk ih
    simpa [cumulativeDepth] using
      le_trans ih (Nat.le_add_right _ _)

theorem cumulativeDepth_periodDoubling
    (R : RenormalizationCombinatorics)
    (h : ∀ n, R.period n = 2) :
    ∀ n, cumulativeDepth R n = 2 * n := by
  intro n
  induction n with
  | zero =>
      simp [cumulativeDepth]
  | succ n ih =>
      simp [cumulativeDepth, h, ih, Nat.mul_succ]

theorem not_summable_of_uniform_lower_bound
    {a : ℕ → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (ha : ∀ n, μ ≤ a n) :
    ¬ Summable a := by
  intro hsum
  have hlim := hsum.tendsto_atTop_zero
  rw [Metric.tendsto_atTop] at hlim
  specialize hlim (μ / 2) (by positivity)
  rcases hlim with ⟨N, hN⟩
  have hdist : dist (a N) 0 < μ / 2 :=
    hN N le_rfl
  have hnonneg : 0 ≤ a N :=
    le_trans (le_of_lt hμ) (ha N)
  have hlt : a N < μ / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hdist
  exact (not_lt_of_ge (ha N))
    (lt_of_lt_of_le hlt (by nlinarith [hμ]))

theorem not_summable_of_aPrioriBounds
    {Tower : Type*} (B : APrioriBounds Tower) (T : Tower) :
    ¬ Summable (fun n => B.modulus T n) :=
  not_summable_of_uniform_lower_bound B.lower_bound_pos
    (fun n => B.modulus_ge T n)

end

end Literature
end MLC
