import Mlc.Research.CaseTree

/-!
# The published cases of the reduction

The classes of `Mlc/Research/CaseTree.lean` that Dudko's survey treats by published theorems.
Each is one lemma about the geometric dictionary, with its source. None is proved here: they
are hypotheses of the programme, not formalized, and they are listed apart from Problems 4.3
and 4.4 because the literature proves them.

* `Yoccoz`: the parameters that are not infinitely renormalizable
  (Yoccoz's theorem, reduction (2.1) of §2; Hubbard; Milnor).
* `BoundedTypeInputs`: Theorem 4.1 (Dudko–Lyubich, with Kahn's bounded primitive
  combinatorics): for bounded relative periods the Teichmüller contraction and the
  dichotomy (4.6) hold. The a priori bounds follow (`WidthTower.aPrioriBounds_of_bounded`).
* `AntiMoleculeInputs`: §4.1–§4.2 (Kahn–Lyubich: Covering Lemma and Quasi-Additivity Law), the
  amplification (4.3) and (4.5) for primitive levels far from the Molecule.
* `Neutral`: Theorem 4.2 (Dudko–Lyubich: pseudo-Siegel a priori bounds for all neutral
  quadratic polynomials) together with the sectorial bounds of §3.4, and the passage to the
  local connectivity of `M` at the neutral parameters.
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

/-- **Lemma B** (Theorem 4.1 for the bounded type). The Teichmüller contraction and the
dichotomy (4.6) hold for the tower of a parameter of bounded type. -/
def BoundedTypeInputs : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, c ∉ interior MLC.Quadratic.MandelbrotSet →
    G.cls c = .boundedType →
      ∃ T, G.tower c = some T ∧ T.Teichmuller ∧ T.Dichotomy

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

theorem hasBound_of_bounded (hB : G.BoundedTypeInputs) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hcls : G.cls c = .boundedType) : ∃ B, G.HasBound c B := by
  obtain ⟨T, hT, P, hP⟩ := G.bounded_spec c hcls
  obtain ⟨T', hT', hTeich, hDich⟩ := hB c hc hi hcls
  have hTT : T' = T := Option.some.inj (hT'.symm.trans hT)
  subst hTT
  obtain ⟨B, hBd⟩ := T'.aPrioriBounds_of_bounded hP hTeich hDich
  exact ⟨B, lt_of_lt_of_le (T'.width_pos 0) (hBd 0), T', hT', hBd⟩

theorem hasBound_of_antiMolecule (hA : G.AntiMoleculeInputs) {c : ℂ}
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) (hi : c ∉ interior MLC.Quadratic.MandelbrotSet)
    (hcls : G.cls c = .antiMolecule) : ∃ B, G.HasBound c B := by
  obtain ⟨T, hT, hS⟩ := hA c hc hi hcls
  obtain ⟨B, hBd⟩ := T.aPrioriBounds_of_strongAmplification hS
  exact ⟨B, lt_of_lt_of_le (T.width_pos 0) (hBd 0), T, hT, hBd⟩

end Geometry

end

end MLC.Research
