import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace MLC

namespace Quadratic

open Complex Topology Set Filter

noncomputable section

/-!
Reductions around puzzle-annulus moduli.

This file provides a single general-purpose lemma: a uniform positive lower bound on a
sequence of nonnegative reals forces the series to diverge.
-/

theorem not_summable_of_lower_bound {f : ℕ → ℝ} {m : ℝ}
    (hm : 0 < m) (h : ∀ n : ℕ, m ≤ f n) : ¬ Summable f := by
  intro hs
  have h0 : Tendsto f atTop (𝓝 (0 : ℝ)) := hs.tendsto_atTop_zero
  have hlt : ∀ᶠ n in atTop, f n < m / 2 :=
    (tendsto_order.1 h0).2 (m / 2) (by linarith)
  have hge : ∀ᶠ n in atTop, m ≤ f n := Filter.Eventually.of_forall h
  rcases (hge.and hlt).exists with ⟨n, hn_ge, hn_lt⟩
  linarith

end

end Quadratic

end MLC
