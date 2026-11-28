import Mlc.Research.Published

/-!
# Problem 4.3, decomposed

> **Problem 4.3.** Establish pseudo-Siegel a priori bounds in the remaining unbounded
> satellite ql cases. (Dudko, arXiv:2512.24171, §4.4.)

The proof of Theorem 4.1 (§4.3) gives a priori bounds for towers of bounded type in two
steps: the dichotomy (4.6), and the exclusion of its second alternative (a jump of the
degeneration by `C_δ`) by the Teichmüller contraction, which bounds the jump by a factor
`Δ^p` that depends on the relative period `p` (§4.3, "Alternative (ii) is prevented by the
Teichmüller contraction"). For relative periods that are not bounded, each step fails in
exactly one place:

* the factor of the jump is unbounded, so `C_δ` cannot be chosen above it;
* the additive error `O_{p_n}(1)` of the amplification (4.3) depends on the period without
  a control (§4.2: "the period `p_n` is assumed to be big but still bounded"). The published
  constants depend on `p` implicitly: the threshold `M(p)` of Kahn's theorem, the constant
  `C_{δ,P}` of the Wave Lemma estimate and the threshold of the Covering Lemma are not given
  as functions of `p`. A decomposition with a linear topological error is known (Kahn–Lyubich,
  arXiv:2601.21905, Theorem 3.9: `W(S) − O(|χ(S)|) ≤ 2 ∑ W(α) ≤ W(S)`), which is the evidence
  for the linear error below, but it is not the dynamical dichotomy.

**What is bounded.** The quadratic-like degeneration `W(f_k)` of (4.1) is unbounded in some
classes of unbounded satellite type: Sørensen's examples and the class `QG_N` of
Cheraghi–Shishikura lack quadratic-like a priori bounds (arXiv:1509.07843, abstract and
§1.4). The problem asks for *pseudo-Siegel* a priori bounds, so, in the reading proposed here,
the widths of the tower of an unbounded satellite parameter (`Geometry.tower`, see
`CaseTree.lean`) are the pseudo-Siegel degenerations: the degeneration of a level once the
pseudo-Siegel disks of its near-neutral steps have consumed the invariant degeneration (§4,
"pseudo-Siegel disks are constructed to consume most of the invariant degeneration"). In the
neutral case such bounds hold uniformly in the size of the continued-fraction entries
(Theorem 4.2; Dudko–Lyubich, arXiv:2210.09280, Theorems 1.1–1.3). The class `QG_N` itself is
the published class `Geometry.QuadraticGrowth`, so Problem 4.3 concerns the unbounded
satellite parameters outside it.

`WidthTower.aPrioriBounds_of_jumpCap` shows that two statements suffice for the a priori
bounds, whatever the relative periods are: a **cap on the jumps** (a jump by a fixed factor
`C₀` lands below a fixed ceiling `B₀`), and an additive error at most linear in the period
(each of the `p` small Julia sets contributes a bounded error). The cap is the weakest
hypothesis of its kind: a priori bounds imply it (`aPrioriBounds_iff_jumpCap`), and a uniform
growth bound, which an earlier version of this module asked for, is stronger. At the levels of
small relative period the Teichmüller contraction caps the jumps, so the cap is needed only at
the levels of large relative period (`aPrioriBounds_of_tails`). `WidthTower.uniformities_necessary`
shows that neither ingredient can be dropped. So, in the reading proposed here, Problem 4.3 is
the three lemmas below: the Teichmüller contraction for the pseudo-Siegel degeneration (the
version for the quadratic-like degeneration of bounded type is published,
`Geometry.TeichmullerContraction`), the cap, and the linear dichotomy.

The survey does not state the lemmas. It states that pseudo-Siegel disks are constructed to
consume most of the invariant degeneration in the neutral case (Theorem 4.2, the left loop of
Figure 14), which is the degeneration that alternative (ii) amplifies at deeper levels, and
that the right loop of Figure 14, the antirenormalization relative to `β`, is the strategy for
the remaining near-neutral satellite cases. The neutral case is the model situation, and the
lemmas transport its mechanism to the satellite situation.

The sub-steps through which the lemmas are expected to be proved (proposed, not formalized):

* **PS1** nested pseudo-Siegel disks `Ẑ^{[m]}`, almost invariant up to `q^{[m+1]}`
  iterations, exist at the satellite levels of large relative period, with `Ẑ^{-1}`, `Ẑ^0`
  uniformly quasiconformal (the satellite analogue of (4.7));
* **PS2** the non-invariance error of `Ẑ^{[m]}` is bounded by a geometric series, because the
  antirenormalization relative to `β` is contracting;
* **PS3** `Ẑ^{-1}` is obtained from `Ẑ^0` by adding a parabolic fjord bounded by a dam in an
  invariant rectangle;
* **PS4** the degeneration along combinatorially invariant rectangles is absorbed by `Ẑ^{[m]}`
  (Figure 13, "if `G` is invariant rel `δ`, then `W(G ∖ G') ≥ C_δ W(G)`"): in a jump of
  alternative (ii) the deeper degeneration is bounded by the uniform quasiconformal geometry
  of the disks (PS1–PS4 give `UnboundedJumpCap`), and the same estimate with the Wave Lemma
  gives the amplification with an error linear in the period (`UnboundedDichotomy`). The
  arithmetic of the estimate `W(G ∖ G') ≥ δ⁻¹ W(G)` is proved as an implication in
  `Mlc/Research/ExtremalLength.lean` (`extWidth_ge_of_series`: if the curves of a family cross two
  disjoint regions in succession and the second piece carries the fraction `1 − δ` of the
  extremal length, the first has width at least `δ⁻¹` times that of the whole); that the
  families of Figure 13 satisfy these hypotheses is the dynamical content and is not formalized.

`UnboundedTeichmuller` is proposed to follow from the published contraction: at the levels
whose rotation number is away from `0` there is no regularization (`Ẑ^0 = Ẑ^{-1}`, §4.4), so
the pseudo-Siegel degeneration is the quadratic-like one there, and the pullback estimate
applies.
-/

namespace MLC.Research

open Set

noncomputable section

namespace Geometry

variable (G : Geometry)

/-- **Lemma TC′ (Problem 4.3).** At a parameter of the class of unbounded satellite type, the
pseudo-Siegel degeneration of the levels grows from a level to the next by at most a factor
`Δ_P` that depends on the bound `P` of the relative period of the level: the Teichmüller
contraction `Geometry.TeichmullerContraction` for the pseudo-Siegel degeneration. -/
def UnboundedTeichmuller : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .unboundedSatellite →
      ∃ T, G.tower c = some T ∧ T.Teichmuller

/-- **Lemma G (Problem 4.3).** At a parameter of the class of unbounded satellite type, a jump
of the pseudo-Siegel degeneration by a fixed factor `C₀` at a level of large relative period
lands below a fixed ceiling `B₀`: the invariant degeneration that alternative (ii) amplifies
is absorbed by the pseudo-Siegel disks (PS1–PS4). -/
def UnboundedJumpCap : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .unboundedSatellite →
      ∃ T, G.tower c = some T ∧
        ∃ (P₀ : ℕ) (C₀ B₀ : ℝ), 0 < C₀ ∧ T.LargePeriodJumpCap P₀ C₀ B₀

/-- **Lemma D (Problem 4.3).** At a parameter of the class of unbounded satellite type, the
dichotomy (4.6) holds for the pseudo-Siegel degeneration with an additive error at most linear
in the period: either the amplification (4.3) holds, or the degeneration jumps by the factor
`C_δ`. -/
def UnboundedDichotomy : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .unboundedSatellite →
      ∃ T, G.tower c = some T ∧ T.LinearDichotomy

/-- Lemmas TC′, G and D give a priori bounds for the pseudo-Siegel degeneration at the
parameters of unbounded satellite type. -/
theorem hasBound_of_unbounded (hTC : G.UnboundedTeichmuller) (hG : G.UnboundedJumpCap)
    (hD : G.UnboundedDichotomy) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hcls : G.cls c = .unboundedSatellite) : ∃ B, G.HasBound c B := by
  obtain ⟨T, hT, P₀, C₀, B₀, hC, hL⟩ := hG c hc hi hcls
  obtain ⟨T₁, hT₁, hTeich⟩ := hTC c hc hi hcls
  obtain ⟨T₂, hT₂, hDich⟩ := hD c hc hi hcls
  have e₁ : T₁ = T := Option.some.inj (hT₁.symm.trans hT)
  have e₂ : T₂ = T := Option.some.inj (hT₂.symm.trans hT)
  rw [e₁] at hTeich
  rw [e₂] at hDich
  obtain ⟨B, hBd⟩ := T.aPrioriBounds_of_tails hC hTeich hL hDich
  exact ⟨B, lt_of_lt_of_le (T.width_pos 0) (hBd 0), T, hT, hBd⟩

end Geometry

end

end MLC.Research
