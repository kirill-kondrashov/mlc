import Mlc.Research.CaseTree
import Mlc.Research.NestModulus
import Mlc.Research.DivergentNest

/-!
# The phase–parameter relation in moduli form

Lemma T (`Geometry.Transfer`) turns an a priori bound on the degeneration of the tower of `c`
into a connected parameter nest whose pieces shrink to `c`. Its proof in the literature has two
halves (Kahn–Lyubich; Lyubich, the phase–parameter relation; Dudko §3.9, §4.1–§4.3):

* the *dynamical half* builds, from the bound, a nest of parameter pieces around `c` whose
  annuli have moduli with an infinite sum (the moduli of the dynamical annuli of the tower
  transfer to the parameter plane by the quasi-additivity law and the phase–parameter
  relation);
* the *geometric half* shows that such a nest shrinks to `c`, and so gives the separation
  estimate of every budget (the Grötzsch–Teichmüller estimate).

`Mlc/Research/NestModulus.lean` proves the geometric half. This module states the dynamical half
as `Geometry.PhaseParameter`, derives the transfer lemma from it, and proves the converse
(`Mlc/Research/DivergentNest.lean`: every shrinking nest has a subnest whose moduli add up to
infinity), so that the two statements are equivalent. The moduli form is thus a lossless
reformulation of Lemma T in the language of the phase–parameter relation, and what is open is the
same construction of the nest from an a priori bound.
-/

namespace MLC.Research

open MeasureTheory

noncomputable section

namespace Geometry

variable (G : Geometry)

/-- **The phase–parameter relation, in moduli form.** An a priori bound on the degeneration of
the tower of `c` gives a connected nest of parameter pieces around `c` in the Mandelbrot set
whose annuli have moduli with an infinite sum. -/
def PhaseParameter : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, ∀ (B : ℝ) (_ : 0 < B), G.HasBound c B →
    ∃ D : ConnectedNest MLC.Quadratic.MandelbrotSet c, D.DivergentModuli

/-- **Lemma T from the phase–parameter relation.** The moduli of the annuli of the nest add up
to infinity, so the pieces shrink to `c` and the separation estimate holds for every budget. -/
theorem transfer_of_phaseParameter (h : G.PhaseParameter) : G.Transfer := by
  intro c hc B hB hbound
  obtain ⟨D, hD⟩ := h c hc B hB hbound
  exact D.nonempty_parameterRealization hD _

/-- **The moduli form follows from Lemma T.** The nest of Lemma T shrinks to `c`, because its
separation estimate has a divergent budget, and a shrinking nest has a subnest whose moduli add up
to infinity. -/
theorem phaseParameter_of_transfer (h : G.Transfer) : G.PhaseParameter := by
  intro c hc B hB hbound
  obtain ⟨⟨D, hsep⟩⟩ := h c hc B hB hbound
  have hbudget := (ReturnBudget.ofBound B hB).unbounded_of_linearLossControl
    (ReturnBudget.ofBound_linearLossControl B hB)
  exact D.exists_divergentSubnest fun ε hε => D.exists_closure_subset_ball hsep hbudget hε

/-- **Lemma T is equivalent to the phase–parameter relation in moduli form.** -/
theorem transfer_iff_phaseParameter : G.Transfer ↔ G.PhaseParameter :=
  ⟨G.phaseParameter_of_transfer, G.transfer_of_phaseParameter⟩

end Geometry

end

end MLC.Research
