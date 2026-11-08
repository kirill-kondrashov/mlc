import Mathlib

/-!
# Nested sets with shrinking diameters

In Lyubich's *Dynamics of quadratic polynomials III* (Asterisque 261), Proposition 6.4, the nested
Mandelbrot copies `M_n` attached to a combinatorial class have diameters tending to zero, so the
class `⋂ M_n` consists of a single point.  This module proves that topological step in an arbitrary
metric space.  It does not formalize bounded shape, fine families, or the parapuzzle geometry.
-/

open Set Filter Topology Metric

namespace MLC.Literature

variable {X : Type*} [MetricSpace X]

/-- Bounded sets whose diameters tend to zero have at most one common point. -/
theorem subsingleton_iInter_of_diam_tendsto_zero (K : ℕ → Set X)
    (hbdd : ∀ n, Bornology.IsBounded (K n)) (hdiam : Tendsto (fun n => diam (K n)) atTop (𝓝 0)) :
    (⋂ n, K n).Subsingleton := by
  intro x hx y hy
  have hxy : ∀ n, dist x y ≤ diam (K n) := fun n =>
    dist_le_diam_of_mem (hbdd n) (mem_iInter.mp hx n) (mem_iInter.mp hy n)
  exact dist_le_zero.mp (ge_of_tendsto' hdiam hxy)

/-- A decreasing sequence of nonempty compact sets whose diameters tend to zero meets in exactly one point. -/
theorem exists_unique_mem_iInter_of_antitone (K : ℕ → Set X) (hanti : Antitone K)
    (hcomp : ∀ n, IsCompact (K n)) (hne : ∀ n, (K n).Nonempty)
    (hdiam : Tendsto (fun n => diam (K n)) atTop (𝓝 0)) :
    ∃! x, x ∈ ⋂ n, K n := by
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
      (fun n => hanti (Nat.le_succ n)) hne (hcomp 0) (fun n => (hcomp n).isClosed)
  exact ⟨x, hx, fun y hy =>
    subsingleton_iInter_of_diam_tendsto_zero K (fun n => (hcomp n).isBounded) hdiam hy hx⟩

end MLC.Literature
