import Mlc.Research.CaseTree

/-!
# Problem 4.3, decomposed

> **Problem 4.3.** Establish pseudo-Siegel a priori bounds in the remaining unbounded
> satellite ql cases. (Dudko, arXiv:2512.24171, §4.4.)

The proof of Theorem 4.1 (§4.3) gives a priori bounds for towers of bounded type in two
steps: the dichotomy (4.6), and the exclusion of its second alternative (a jump of the
degeneration by `C_δ`) by the Teichmüller contraction, which bounds the jump by a factor
`Δ^p` that depends on the relative period `p` (§4.3, "Alternative (ii) is prevented by the
Teichmüller contraction"). For relative periods that are not bounded, both steps fail in
exactly one place each:

* the factor of the jump is not uniform, so `C_δ` cannot be chosen above it;
* the additive error `O_{p_n}(1)` of the amplification (4.3) is not uniform
  (§4.2: "the period `p_n` is assumed to be big but still bounded").

`WidthTower.aPrioriBounds_of_uniform` shows that these two uniformities suffice for the a
priori bounds, whatever the relative periods are. So, in the reading proposed here, Problem
4.3 is the pair of lemmas below. The survey does not state them: it states that pseudo-Siegel
disks absorb the invariant degeneration in the neutral case (Theorem 4.2, the left loop of
Figure 14) and that the right loop of Figure 14, the antirenormalization relative to `β`,
is the strategy for the remaining near-neutral satellite cases.

The sub-steps through which the lemmas are expected to be proved (proposed, not formalized):

* **PS1** nested pseudo-Siegel disks `Ẑ^{[m]}`, almost invariant up to `q^{[m+1]}`
  iterations, exist at the satellite levels of large relative period, with `Ẑ^{-1}`, `Ẑ^0`
  uniformly quasiconformal (the satellite analogue of (4.7));
* **PS2** the non-invariance error of `Ẑ^{[m]}` is bounded by a geometric series, because the
  antirenormalization relative to `β` is contracting;
* **PS3** `Ẑ^{-1}` is obtained from `Ẑ^0` by adding a parabolic fjord bounded by a dam in an
  invariant rectangle;
* **PS4** the degeneration along combinatorially invariant rectangles is absorbed by `Ẑ^{[m]}`
  (Figure 13, "if `G` is invariant rel `δ`, then `W(G ∖ G') ≥ C_δ W(G)`"), which gives the
  growth bound uniformly in the relative period (PS1–PS4 give `UnboundedGrowth`), and
  the same estimate with the Wave Lemma gives the amplification with a uniform error
  (`UnboundedDichotomy`).
-/

namespace MLC.Research

open Set

noncomputable section

namespace Geometry

variable (G : Geometry)

/-- **Lemma G (Problem 4.3).** At a parameter of the class of unbounded satellite type the
degeneration grows by at most a fixed factor `Δ` from a level to the next, however large
the relative period of the satellite level is. This is the uniform version of the Teichmüller
contraction, expected from the pseudo-Siegel disks (PS1–PS4). -/
def UnboundedGrowth : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .unboundedSatellite →
      ∃ T Δ, G.tower c = some T ∧ T.GrowthBound Δ

/-- **Lemma D (Problem 4.3).** At a parameter of the class of unbounded satellite type, the
dichotomy (4.6) holds with an additive error that does not depend on the period: either the
amplification (4.3) holds, or the degeneration jumps by the factor `C_δ`. -/
def UnboundedDichotomy : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .unboundedSatellite →
      ∃ T, G.tower c = some T ∧ T.UniformDichotomy

/-- Lemmas G and D give a priori bounds at the parameters of unbounded satellite type. -/
theorem hasBound_of_unbounded (hG : G.UnboundedGrowth) (hD : G.UnboundedDichotomy) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hcls : G.cls c = .unboundedSatellite) : ∃ B, G.HasBound c B := by
  obtain ⟨T, Δ, hT, hΔ⟩ := hG c hc hi hcls
  obtain ⟨T', hT', hDich⟩ := hD c hc hi hcls
  have hTT : T' = T := Option.some.inj (hT'.symm.trans hT)
  subst hTT
  obtain ⟨B, hBd⟩ := T'.aPrioriBounds_of_uniform hΔ hDich
  exact ⟨B, lt_of_lt_of_le (T'.width_pos 0) (hBd 0), T', hT', hBd⟩

end Geometry

end

end MLC.Research
