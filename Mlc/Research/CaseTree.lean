import Mlc.Research.Degeneration
import Mlc.Research.VirtualMolecule

/-!
# The case tree of the MLC reduction

Dudko's survey reduces the local connectivity of `M` at a boundary parameter `c` to a priori
bounds for the quadratic-like renormalization tower of `c`, case by case (§1.2, §2, §4). This
module fixes the cases and the interface through which the geometric statements enter.

* `BoundaryClass` lists the cases, by the combinatorial type of the renormalization of `c`.
* `Geometry` is the dictionary: it assigns to a parameter its class, the tower with the
  degeneration of its levels, and the tower with the degeneration of its virtual levels
  (§4.5). The dictionary is a parameter of every statement; its faithfulness to the
  dynamics of `f_c` is the content of the lemmas below, none of which is proved here.
* `Geometry.system` is the candidate system of the towers with a priori bounds. A bound `B`
  on the degeneration gives the canonical return budget `ReturnBudget.ofBound B`, and the
  lemma `Geometry.Transfer` (the phase–parameter transfer of Kahn–Lyubich and Lyubich) turns it into a
  parameter realization.
* The published cases are one lemma each (`yoccoz`, `teichmuller`, `boundedType`,
  `antiMolecule`, `neutral`, `quadraticGrowth` in `Mlc/Research/Published.lean`); Problems 4.3
  and 4.4 are decomposed in `Mlc/Research/Problem43.lean` and `Mlc/Research/Problem44.lean`.

The classes are not defined by the conclusion: each is a combinatorial type of the
renormalization of `c`.
-/

namespace MLC.Research

open Set

noncomputable section

/-- The cases of the reduction of MLC at a boundary parameter, by the type of the
renormalization of `c` (Dudko §1.2, §2, §4). -/
inductive BoundaryClass
  /-- `c` is not infinitely quadratic-like renormalizable (non-renormalizable or finitely
  renormalizable): Yoccoz, Hubbard. -/
  | finite
  /-- `c` is irrationally indifferent, on the boundary of the main cardioid or at the end of a
  finite tower: the near-neutral levels of §4.4 (Theorem 4.2). -/
  | neutral
  /-- infinitely renormalizable with bounded relative periods, primitive or satellite
  (Theorem 4.1: Kahn; Dudko–Lyubich). -/
  | boundedType
  /-- infinitely renormalizable, primitive levels far from the Molecule with large relative
  periods (§4.2: Kahn–Lyubich, the anti-Molecule condition). -/
  | antiMolecule
  /-- infinitely satellite renormalizable with a type sequence of quadratic growth, the class
  `QG_N` of Theorem D of Cheraghi–Shishikura: the relative periods are unbounded, and the
  near-parabolic renormalization gives the local connectivity without quadratic-like a priori
  bounds. -/
  | quadraticGrowth
  /-- infinitely renormalizable with unbounded relative periods at satellite levels, outside
  the class of quadratic growth: Problem 4.3. -/
  | unboundedSatellite
  /-- primitive level close to the Molecule, with a long virtual satellite chain of bounded
  relative periods: the first subcase of Problem 4.4 (§4.5). -/
  | virtualBounded
  /-- primitive level close to the Molecule, with a virtual near-neutral step: the second
  subcase of Problem 4.4 (§4.5). -/
  | virtualNearNeutral
  deriving DecidableEq

/-- The geometric dictionary of the programme. It assigns to a parameter its class, the
tower of its renormalizations with the degeneration of the levels, and the tower of its
virtual levels (the satellite chain of §4.5). Faithfulness of the dictionary to `f_c` is not
a field: it is the content of the lemmas that take the dictionary as a parameter.

The width of a level is the quadratic-like degeneration `W(f_k)` of (4.1) in the classes
that the quadratic-like theory treats. In the class `unboundedSatellite` it is the
*pseudo-Siegel* degeneration: the degeneration of the level once the pseudo-Siegel disks
of its near-neutral steps have consumed the invariant degeneration of the parabolic fjords
(§4, before §4.1). The quadratic-like degeneration is unbounded in some classes of unbounded
satellite type (Sørensen; Cheraghi–Shishikura, §1.4: they lack a priori bounds), so a bound
on it is not what Problem 4.3 asks for; Problem 4.3 asks for the bounds of the pseudo-Siegel
degeneration. -/
structure Geometry where
  cls : ℂ → BoundaryClass
  tower : ℂ → Option WidthTower
  vtower : ℂ → Option WidthTower
  /-- The class of bounded type means bounded relative periods. -/
  bounded_spec :
    ∀ c, cls c = .boundedType → ∃ T, tower c = some T ∧ ∃ P : ℕ, ∀ k, T.rel k ≤ P
  /-- The virtual chain of the first subcase has bounded relative periods. -/
  virtualBounded_spec :
    ∀ c, cls c = .virtualBounded → ∃ T, vtower c = some T ∧ ∃ P : ℕ, ∀ k, T.rel k ≤ P

namespace Geometry

variable (G : Geometry)

/-- A degeneration bound `B` for the tower of `c`. -/
def HasBound (c : ℂ) (B : ℝ) : Prop :=
  0 < B ∧ ∃ T, G.tower c = some T ∧ ∀ k, T.width k ≤ B

/-- The candidate system of the towers with a priori bounds: a parameter is admissible with the
canonical budget of a degeneration bound, or with any budget that has a realization. -/
def system : CandidateSystem where
  admissible c b :=
    (∃ (B : ℝ) (hB : 0 < B), G.HasBound c B ∧ b = ReturnBudget.ofBound B hB) ∨
      Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b)

/-- **Lemma T (phase–parameter transfer).** An a priori bound on the degeneration of the
tower of `c` yields a connected parameter nest with the separation estimate of the canonical
budget. This is the step from a priori bounds to the shrinking of the parameter pieces, by
the quasi-additivity law of Kahn–Lyubich and the phase–parameter relation of Lyubich
(§3.9, §4.1–§4.3). -/
def Transfer : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, ∀ (B : ℝ) (hB : 0 < B), G.HasBound c B →
    Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c (ReturnBudget.ofBound B hB))

/-- The system of the towers with a priori bounds has a realization, given the transfer. -/
theorem system_realization (hT : G.Transfer) : G.system.Realization := by
  intro c hc b hb _
  rcases hb with ⟨B, hB, hBound, rfl⟩ | hreal
  · exact hT c hc B hB hBound
  · exact hreal

/-- A tower with a degeneration bound is eligible. -/
theorem eligible_of_hasBound {c : ℂ} {B : ℝ} (h : G.HasBound c B) : G.system.Eligible c :=
  ⟨ReturnBudget.ofBound B h.1, Or.inl ⟨B, h.1, h, rfl⟩,
    ReturnBudget.ofBound_linearLossControl B h.1⟩

/-- A parameter with a realization of a budget with linear loss is eligible. -/
theorem eligible_of_realization {c : ℂ} {b : ReturnBudget}
    (hr : Nonempty (ParameterRealization MLC.Quadratic.MandelbrotSet c b))
    (hl : b.LinearLossControl) : G.system.Eligible c :=
  ⟨b, Or.inr hr, hl⟩

end Geometry

end

end MLC.Research
