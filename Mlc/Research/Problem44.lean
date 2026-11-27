import Mlc.Research.CaseTree
import Mlc.Research.VirtualMolecule

/-!
# Problem 4.4, decomposed

> **Interpolation Problem 4.4.** Develop a Virtual Molecule version of the Near-Degenerate
> Regime. (Dudko, arXiv:2512.24171, §4.5.)

For a parameter whose first quadratic-like renormalization is primitive, encoded by a maximal
primitive copy `M₁ ⊂ M`, there is a canonical chain of satellite copies
`M = M^(0) ⊋ M^(1) ⊋ ⋯ ⊋ M^(n+1)`, and `M₁` is close to the main Molecule if and only if
the period of `M^(n+1)` is large. The puzzle levels of §4.2 control the scales between
`M^(n)` and `M₁` and fail between `M` and `M^(n)`, the *virtual Molecule*. It has two subcases:

* **virtual bounded-type satellite**, `n ≫ 1` with bounded relative periods of `M^(s+1)` rel
  `M^(s)` (the class `virtualBounded`);
* **virtual near-neutral**, `n = 0` (the class `virtualNearNeutral`).

The survey's strategy: *partially invariant virtual Julia sets of `M^(s)`*, the connected hulls
of the Cantor small Julia sets inside `J_f`, which contain the critical orbit only up to an
appropriate number of first returns (`VirtualJuliaNest` in `Mlc/Research/VirtualMolecule.lean`).

The decomposition proposed here follows the three parts of `VirtualMoleculeAPrioriControl`:

* **Lemma VJ** the virtual Julia nest with its hull inside `J_c` and partial invariance;
* **Lemmas VT1, VD1** (first subcase): the Teichmüller contraction and the dichotomy (4.6) for
  the virtual levels of bounded relative periods, so that `WidthTower.aPrioriBounds_of_bounded`
  gives a priori bounds for the virtual degeneration;
* **Lemmas VG2, VD2** (second subcase): the uniform growth bound and the dichotomy with an
  error at most linear in the period for the virtual near-neutral step, which need the
  pseudo-Siegel regularization of Problem 4.3, so that `WidthTower.aPrioriBounds_of_uniform`
  applies;
* **Lemma VT** the virtual phase–parameter transfer: a degeneration bound on the virtual levels
  gives a connected parameter nest, a phase–parameter chart into the virtual hulls and the
  dynamical separation estimate of the canonical budget.

The survey states only the strategy. The lemmas are the proposed reading, as in
`Mlc/Research/Problem43.lean`. In particular the survey describes the near-neutral subcase by
`n = 0`; the class `virtualNearNeutral` here is the one whose virtual levels have a step of
unbounded relative period, which is how the dichotomy of the classes of unbounded relative
periods enters.
-/

namespace MLC.Research

open Set

noncomputable section

namespace Geometry

variable (G : Geometry)

/-- The parameters of the two virtual subcases. -/
def IsVirtual (c : ℂ) : Prop := G.cls c = .virtualBounded ∨ G.cls c = .virtualNearNeutral

/-- **Lemma VJ (Problem 4.4).** A parameter of the virtual Molecule has a partially invariant
virtual Julia set: the connected hull of the Cantor small Julia sets with a finite critical
return window lies inside `J_c`, and the first-return window maps the invariant part into
the hull. -/
def VirtualJulia : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet → G.IsVirtual c →
    ∃ V : VirtualJuliaNest c, V.HullWithinJulia ∧ V.PartialInvariance

/-- **Lemma VT1 (Problem 4.4, virtual bounded type).** The Teichmüller contraction holds for
the virtual levels. -/
def VirtualTeichmuller : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .virtualBounded → ∃ T, G.vtower c = some T ∧ T.Teichmuller

/-- **Lemma VD1 (Problem 4.4, virtual bounded type).** The dichotomy (4.6) holds for the
virtual levels. -/
def VirtualDichotomy : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .virtualBounded → ∃ T, G.vtower c = some T ∧ T.Dichotomy

/-- **Lemma VG2 (Problem 4.4, virtual near-neutral).** The degeneration of the virtual levels
grows by at most a fixed factor from a level to the next. -/
def VirtualGrowth : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .virtualNearNeutral → ∃ T Δ, G.vtower c = some T ∧ T.GrowthBound Δ

/-- **Lemma VD2 (Problem 4.4, virtual near-neutral).** The dichotomy (4.6) holds for the
virtual levels with an additive error at most linear in the period. -/
def VirtualLinearDichotomy : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .virtualNearNeutral → ∃ T, G.vtower c = some T ∧ T.LinearDichotomy

/-- **Lemma VT (Problem 4.4).** The virtual phase–parameter transfer: a degeneration bound
on the virtual levels gives a connected parameter nest, a phase–parameter chart into the
virtual hulls, and the dynamical separation estimate of the canonical budget. -/
def VirtualTransfer : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, G.IsVirtual c →
    ∀ V : VirtualJuliaNest c, V.HullWithinJulia → V.PartialInvariance →
      ∀ (B : ℝ) (hB : 0 < B), (∃ T, G.vtower c = some T ∧ ∀ k, T.width k ≤ B) →
        ∃ (D : ConnectedNest MLC.Quadratic.MandelbrotSet c) (_ : VirtualPhaseParameter c V D),
          V.SeparationEstimate (ReturnBudget.ofBound B hB).cost

/-- The lemmas VT1, VD1, VG2 and VD2 give a priori bounds for the virtual degeneration. -/
theorem virtual_hasBound (hT1 : G.VirtualTeichmuller) (hD1 : G.VirtualDichotomy)
    (hG2 : G.VirtualGrowth) (hD2 : G.VirtualLinearDichotomy) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hv : G.IsVirtual c) :
    ∃ (B : ℝ), 0 < B ∧ ∃ T, G.vtower c = some T ∧ ∀ k, T.width k ≤ B := by
  rcases hv with h1 | h2
  · obtain ⟨T, hT, P, hP⟩ := G.virtualBounded_spec c h1
    obtain ⟨T1, hT1', hTeich⟩ := hT1 c hc hi h1
    obtain ⟨T2, hT2', hDich⟩ := hD1 c hc hi h1
    have e1 : T1 = T := Option.some.inj (hT1'.symm.trans hT)
    have e2 : T2 = T := Option.some.inj (hT2'.symm.trans hT)
    rw [e1] at hTeich
    rw [e2] at hDich
    obtain ⟨B, hBd⟩ := T.aPrioriBounds_of_bounded hP hTeich hDich
    exact ⟨B, lt_of_lt_of_le (T.width_pos 0) (hBd 0), T, hT, hBd⟩
  · obtain ⟨T, Δ, hT, hΔ⟩ := hG2 c hc hi h2
    obtain ⟨T', hT', hDich⟩ := hD2 c hc hi h2
    have e : T' = T := Option.some.inj (hT'.symm.trans hT)
    rw [e] at hDich
    obtain ⟨B, hBd⟩ := T.aPrioriBounds_of_uniform hΔ hDich
    exact ⟨B, lt_of_lt_of_le (T.width_pos 0) (hBd 0), T, hT, hBd⟩

/-- **Virtual a priori control.** The lemmas of Problem 4.4 give the a priori-control package of
the virtual Molecule at every parameter of the two virtual subcases. -/
theorem virtualControl (hJ : G.VirtualJulia) (hT1 : G.VirtualTeichmuller)
    (hD1 : G.VirtualDichotomy) (hG2 : G.VirtualGrowth) (hD2 : G.VirtualLinearDichotomy)
    (hVT : G.VirtualTransfer) {c : ℂ} (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hi : c ∉ interior MLC.Quadratic.MandelbrotSet) (hv : G.IsVirtual c) :
    Nonempty (VirtualMoleculeAPrioriControl c) := by
  obtain ⟨V, hV1, hV2⟩ := hJ c hc hi hv
  obtain ⟨B, hB, hbound⟩ := G.virtual_hasBound hT1 hD1 hG2 hD2 hc hi hv
  obtain ⟨D, P, hsep⟩ := hVT c hc hv V hV1 hV2 B hB hbound
  exact ⟨{ virtualJulia := V
           hullWithinJulia := hV1
           partialInvariance := hV2
           budget := ReturnBudget.ofBound B hB
           parameterNest := D
           phaseParameter := P
           linearLossControl := ReturnBudget.ofBound_linearLossControl B hB
           dynamicSeparationEstimate := hsep }⟩

end Geometry

end

end MLC.Research
