import Mlc.Research.CaseTree

/-!
# The published cases of the reduction

The classes of `Mlc/Research/CaseTree.lean` that Dudko's survey treats by published theorems.
Each is one lemma about the geometric dictionary, with its source. None is proved here: they
are hypotheses of the programme, not formalized, and they are listed apart from Problems 4.3
and 4.4 because the literature proves them.

* `Yoccoz`: the parameters that are not infinitely renormalizable
  (Yoccoz's theorem, reduction (2.1) of §2; Hubbard; Milnor).
* `TeichmullerContraction`: for a tower of bounded type, the degeneration of the levels grows
  from a level to the next by a factor that depends only on the relative period (§4.3,
  "Alternative (ii) is prevented by the Teichmüller contraction"). The sources state it for
  towers whose relative periods are bounded by `P`, with a factor `Δ_P` that depends on `P`:
  Dudko–Lyubich, arXiv:2309.02107, Proposition 2.7 (`W(Y_n ∖ X_n) = O(Δ_P^n)`). The version
  for the pseudo-Siegel degeneration of unbounded satellite towers is a lemma of Problem 4.3
  (`UnboundedTeichmuller`).
* `BoundedTypeInputs`: Theorem 4.1 (Dudko–Lyubich, with Kahn's bounded primitive
  combinatorics): the dichotomy (4.6) holds. For bounded relative periods the a priori bounds
  follow with the Teichmüller contraction (`WidthTower.aPrioriBounds_of_bounded`).
* `AntiMoleculeInputs`: §4.1–§4.2 (Kahn–Lyubich: Covering Lemma and Quasi-Additivity Law), the
  amplification (4.3) and (4.5) for primitive levels far from the Molecule.
* `Neutral`: Theorem 4.2 (Dudko–Lyubich: pseudo-Siegel a priori bounds for all neutral
  quadratic polynomials) together with the sectorial bounds of §3.4, and the passage to the
  local connectivity of `M` at the neutral parameters.
* `QuadraticGrowth`: Theorem D of Cheraghi–Shishikura (arXiv:1509.07843), the local
  connectivity of `M` at the parameters of satellite type whose type sequence has quadratic
  growth. The proof goes through near-parabolic renormalization and does not use
  quadratic-like a priori bounds, which these parameters lack. The class is carved out of the
  unbounded satellite parameters, so that Problem 4.3 concerns the remaining ones.
-/

namespace MLC.Research

open Set

noncomputable section

namespace Geometry

variable (G : Geometry)

/-- **Lemma Y.** At the parameters that are not infinitely quadratic-like renormalizable,
`M` is locally connected: Yoccoz's theorem, in the form of a parameter realization. -/
def Yoccoz : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .finite →
      ∃ b : ReturnBudget, b.LinearLossControl ∧
        Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b)

/-- **Lemma TC** (the Teichmüller contraction, §4.3). For the tower of a parameter of bounded
type, the degeneration grows from a level to the next by at most a factor `Δ_P` that depends
on the bound `P` of the relative period of the level (the survey: `W(f_m) = O(Δ^{p_m})`;
Dudko–Lyubich, arXiv:2309.02107, Proposition 2.7). -/
def TeichmullerContraction : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .boundedType →
      ∃ T, G.tower c = some T ∧ T.Teichmuller

/-- **Lemma B** (Theorem 4.1 for the bounded type). The dichotomy (4.6) holds, with an error
that depends on the period, for the tower of a parameter of bounded type. -/
def BoundedTypeInputs : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .boundedType →
      ∃ T, G.tower c = some T ∧ T.Dichotomy

/-- **Lemma A** (§4.1–§4.2, the anti-Molecule condition). The amplification (4.3) and (4.5)
holds for the tower of a parameter whose primitive levels are far from the Molecule. -/
def AntiMoleculeInputs : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .antiMolecule →
      ∃ T, G.tower c = some T ∧ T.StrongAmplification

/-- **Lemma N** (Theorem 4.2). At the neutral parameters, `M` is locally connected, in the
form of a parameter realization. -/
def Neutral : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .neutral →
      ∃ b : ReturnBudget, b.LinearLossControl ∧
        Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b)

/-- **Lemma QG** (Cheraghi–Shishikura, Theorem D). At the parameters of satellite type whose
type sequence `⟨p_i/q_i⟩` has quadratic growth (`b_{1,1} ≥ N`, `b_{i,j+1} ≥ b_{i,j}²`,
`b_{i+1,1} ≥ q_i²` for the continued fractions of the rotation numbers), the pieces
`M(⟨p_i/q_i⟩_{i ≤ n})` have diameter at most `C λⁿ` and `M` is locally connected, in the form
of a parameter realization. -/
def QuadraticGrowth : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .quadraticGrowth →
      ∃ b : ReturnBudget, b.LinearLossControl ∧
        Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b)

theorem hasBound_of_bounded (hTC : G.TeichmullerContraction) (hB : G.BoundedTypeInputs) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hcls : G.cls c = .boundedType) : ∃ B, G.HasBound c B := by
  obtain ⟨T, hT, P, hP⟩ := G.bounded_spec c hcls
  obtain ⟨T₁, hT₁, hTeich⟩ := hTC c hc hi hcls
  obtain ⟨T₂, hT₂, hDich⟩ := hB c hc hi hcls
  have e₁ : T₁ = T := Option.some.inj (hT₁.symm.trans hT)
  have e₂ : T₂ = T := Option.some.inj (hT₂.symm.trans hT)
  rw [e₁] at hTeich
  rw [e₂] at hDich
  obtain ⟨B, hBd⟩ := T.aPrioriBounds_of_bounded hP hTeich hDich
  exact ⟨B, lt_of_lt_of_le (T.width_pos 0) (hBd 0), T, hT, hBd⟩

theorem hasBound_of_antiMolecule (hA : G.AntiMoleculeInputs) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hcls : G.cls c = .antiMolecule) : ∃ B, G.HasBound c B := by
  obtain ⟨T, hT, hS⟩ := hA c hc hi hcls
  obtain ⟨B, hBd⟩ := T.aPrioriBounds_of_strongAmplification hS
  exact ⟨B, lt_of_lt_of_le (T.width_pos 0) (hBd 0), T, hT, hBd⟩

end Geometry

end

end MLC.Research
