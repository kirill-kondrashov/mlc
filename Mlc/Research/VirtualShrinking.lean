import Mlc.Research.Problem44

/-!
# What the virtual separation estimate says

`VirtualJuliaNest.SeparationEstimate cost` is the dynamical estimate that Lemma VT
(`Geometry.VirtualTransfer`, Problem 4.4) must supply on the virtual hulls: for every `ε` there is a
bound `C` such that a point of the closure of the `n`-th hull that is `ε`-far from its origin forces
the partial cost sum `∑_{j<n} cost j` below `C`. For a cost with non-negative terms and divergent
partial sums, such as the canonical cost of a degeneration bound, the estimate is equivalent to the
shrinking of the hulls to their origins (`VirtualJuliaNest.separationEstimate_iff`): every
neighbourhood of the origin of the `n`-th hull contains its closure for `n` large. So the dynamical
content of Lemma VT is that the virtual hulls have diameters that tend to zero
(`Geometry.virtualTransfer_hulls_shrink`), the analogue of the shrinking of the parameter pieces
for Lemma T (`ConnectedNest.separationEstimate_of_shrinking`).
-/

namespace MLC.Research

open Set Metric

noncomputable section

namespace VirtualJuliaNest

variable {c : ℂ} (V : VirtualJuliaNest c)

/-- **The separation estimate of the virtual hulls is their shrinking.** For a cost with
non-negative terms and divergent partial sums, the estimate holds exactly when, for every `ε`, the
closure of the `n`-th hull lies in the `ε`-ball around its origin for `n` large. -/
theorem separationEstimate_iff {cost : ℕ → ℝ} (hnn : ∀ n, 0 ≤ cost n)
    (hunb : UnboundedBudget cost) :
    V.SeparationEstimate cost ↔ ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ n, N ≤ n → closure (V.carrier n) ⊆ ball (V.returns.origin c n) ε := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    obtain ⟨N, hN⟩ := hunb C
    refine ⟨N, fun n hn z hz => ?_⟩
    by_contra hzε
    have hle : ε ≤ dist z (V.returns.origin c n) := not_lt.1 (mem_ball.not.1 hzε)
    have hmono : ∑ j ∈ Finset.range N, cost j ≤ ∑ j ∈ Finset.range n, cost j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) fun j _ _ => hnn j
    exact absurd (hC n z hz hle) (not_le.2 (lt_of_lt_of_le hN hmono))
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨∑ j ∈ Finset.range N, |cost j|, fun n z hz hzε => ?_⟩
    have hnN : n < N := by
      by_contra hn
      exact absurd (mem_ball.1 (hN n (not_lt.1 hn) hz)) (not_lt.2 hzε)
    calc ∑ j ∈ Finset.range n, cost j ≤ ∑ j ∈ Finset.range n, |cost j| :=
          Finset.sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ j ∈ Finset.range N, |cost j| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnN.le)
            fun j _ _ => abs_nonneg _

end VirtualJuliaNest

namespace Geometry

variable (G : Geometry)

/-- **Lemma VT shrinks the virtual hulls.** If the virtual transfer holds, the closure of the
`n`-th virtual hull of a parameter with a degeneration bound on the virtual levels lies in every
neighbourhood of its origin, for `n` large. -/
theorem virtualTransfer_hulls_shrink (hVT : G.VirtualTransfer) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hv : G.IsVirtual c) (V : VirtualJuliaNest c)
    (h1 : V.HullWithinJulia) (h2 : V.PartialInvariance) {B : ℝ} (hB : 0 < B)
    (hbound : ∃ T, G.vtower c = some T ∧ ∀ k, T.width k ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → closure (V.carrier n) ⊆ ball (V.returns.origin c n) ε := by
  obtain ⟨D, P, hsep⟩ := hVT c hc hv V h1 h2 B hB hbound
  have hnn : ∀ n, 0 ≤ (ReturnBudget.ofBound B hB).cost n := fun n =>
    div_nonneg ((ReturnBudget.ofBound B hB).modulus_nonneg _)
      ((ReturnBudget.ofBound B hB).distortion_pos n).le
  have hunb := (ReturnBudget.ofBound B hB).unbounded_of_linearLossControl
    (ReturnBudget.ofBound_linearLossControl B hB)
  exact (V.separationEstimate_iff hnn hunb).1 hsep ε hε

end Geometry

end

end MLC.Research
