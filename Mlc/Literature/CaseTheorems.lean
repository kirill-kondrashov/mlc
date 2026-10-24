import Mlc.Literature.Categorical
import Mlc.Literature.Combinatorics
import Mlc.Literature.Dudko
import Mlc.Literature.PhaseParameter

/-!
# Family-level conditional theorems

The source-specific certificates are useful only when assembled into a family
statement.  This file proves those family-level implications and keeps the
analytic existence hypotheses explicit.
-/

namespace MLC
namespace Literature

noncomputable section

/-- A family of phase--parameter data for finitely renormalizable parameters. -/
def FinitelyRenormalizablePhaseParameterData : Prop :=
  ∀ (c : ℂ) (hc : c ∈ reviewMandelbrotSet),
    FinitelyRenormalizable c →
      Nonempty (PhaseParameterPuzzleData c hc)

theorem finitelyRenormalizableMLC_of_phaseParameterData :
    FinitelyRenormalizablePhaseParameterData →
      FinitelyRenormalizableMLC := by
  intro h c hc hclass
  obtain ⟨data⟩ := h c hc hclass
  exact localConnectivity_of_phaseParameterData data

theorem globalMLC_of_yoccozPhaseParameterResult
    (h : YoccozPhaseParameterResult) :
    GlobalMLC := by
  change LocallyConnectedSpace MLC.mandelbrotSet
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  rcases x with ⟨c, hc⟩
  obtain ⟨data⟩ := h c hc
  exact localConnectivity_of_phaseParameterData data U hU

/-- A family of source-specific literature certificates. -/
def LiteratureCertificateFamily
    (parameterClass : ℂ → Prop) : Prop :=
  ∀ (c : ℂ) (hc : c ∈ reviewMandelbrotSet),
    parameterClass c →
      Nonempty (LiteratureMLCData parameterClass c hc)

theorem pointwiseMLC_of_literatureCertificateFamily
    {parameterClass : ℂ → Prop}
    (h : LiteratureCertificateFamily parameterClass) :
    PointwiseMLCResult parameterClass := by
  intro c hc hclass
  obtain ⟨data⟩ := h c hc hclass
  exact localConnectivity_of_literatureMLCData data

theorem boundedTypeSatelliteMLC_of_certificateFamily
    (isBoundedTypeSatellite : ℂ → Prop)
    (h : LiteratureCertificateFamily isBoundedTypeSatellite) :
    BoundedTypeSatelliteMLC isBoundedTypeSatellite :=
  pointwiseMLC_of_literatureCertificateFamily h

theorem feigenbaumMLC_of_certificateFamily
    (isFeigenbaum : ℂ → Prop)
    (h : LiteratureCertificateFamily isFeigenbaum) :
    FeigenbaumMLC isFeigenbaum :=
  pointwiseMLC_of_literatureCertificateFamily h

theorem parabolicallyBoundedPrimitiveMLC_of_certificateFamily
    (isParabolicallyBoundedPrimitive : ℂ → Prop)
    (h : LiteratureCertificateFamily isParabolicallyBoundedPrimitive) :
    ParabolicallyBoundedPrimitiveMLC isParabolicallyBoundedPrimitive :=
  pointwiseMLC_of_literatureCertificateFamily h

theorem neutralRenormalizationMLC_of_certificateFamily
    (isNeutralRenormalizable : ℂ → Prop)
    (h : LiteratureCertificateFamily isNeutralRenormalizable) :
    PointwiseMLCResult isNeutralRenormalizable :=
  pointwiseMLC_of_literatureCertificateFamily h

end

end Literature
end MLC
