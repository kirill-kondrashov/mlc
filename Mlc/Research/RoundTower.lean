import Mlc.Research.LevelTower

/-!
# Every width tower is realized by round levels

`LevelTower` records, for each level of a `WidthTower`, a filled set and a range domain with
`W_k = 1 / mod(V_k ∖ K_k)`, where the modulus is the extremal width of the `C¹` loops in the annulus
that separate the inner set from the complement of the outer one. Nothing in the structure ties
`filled k` and `target k` to the dynamics of `f_c`. This module records the consequence: every
width tower is the width tower of a level tower whose levels are round annuli
(`WidthTower.exists_levelTower`), with the filled set `B̄(0, 1)` and the range domain `B(0, e^{2π/W_k})`
of modulus `1 / W_k` (`extWidth_loopFamily_round_open`).

So `LevelTower` has no dynamical content by itself. The content of the collar and comparison
hypotheses of `LevelTower.lean` and `CollarCriterion.lean` lies in the sets to which they are
applied: they are statements about the filled Julia sets and the range domains of quadratic-like
restrictions of `f_c`, when the dictionary provides them, and the round realization shows that for
arbitrary sets they say no more than a bound on the widths.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Real Metric

noncomputable section

namespace WidthTower

/-- The level tower of round annuli with the widths of `T`: the level `k` has the filled set
`B̄(0, 1)` and the range domain `B(0, e^{2π/W_k})`. -/
def toLevelTower (T : WidthTower) : LevelTower where
  toWidthTower := T
  filled _ := closedBall 0 1
  target k := ball 0 (Real.exp (2 * π / T.width k))
  width_eq k := by
    have hw := T.width_pos k
    have hR : (1 : ℝ) < Real.exp (2 * π / T.width k) := Real.one_lt_exp_iff.2 (by positivity)
    rw [extWidth_loopFamily_round_open one_pos hR, div_one, Real.log_exp,
      ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    field_simp

/-- **Every width tower is realized by round levels.** The structure `LevelTower` has no dynamical
content by itself: its content is in the hypotheses on the sets of the levels. -/
theorem exists_levelTower (T : WidthTower) : ∃ L : LevelTower, L.toWidthTower = T :=
  ⟨T.toLevelTower, rfl⟩

end WidthTower

end

end MLC.Research
