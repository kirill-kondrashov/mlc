import Mlc.Literature.Renormalization

/-!
# Dudko--Lyubich and current MLC-case contracts

The recent papers prove different analytic estimates, but their parameter-plane
end point has the same shape: a source-specific class predicate together with
connected shrinking parameter pieces.  These certificates keep the common
topological conclusion shared while leaving each analytic proof visible.
-/

namespace MLC
namespace Literature

noncomputable section

/-- Common certificate shape for a literature theorem proving pointwise MLC. -/
structure LiteratureMLCData
    (parameterClass : ℂ → Prop)
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) where
  class_mem : parameterClass c
  parameterPuzzle : ParameterPuzzleBasis c hc
  source_key : String

theorem localConnectivity_of_literatureMLCData
    {parameterClass : ℂ → Prop}
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (data : LiteratureMLCData parameterClass c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  localConnectivity_of_parameterPuzzleBasis data.parameterPuzzle

/-- Dudko--Lyubich bounded-type satellite certificate. -/
abbrev BoundedTypeSatelliteCertificate
    (isBoundedTypeSatellite : ℂ → Prop)
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) :=
  LiteratureMLCData isBoundedTypeSatellite c hc

theorem localConnectivity_of_boundedTypeSatelliteCertificate
    {isBoundedTypeSatellite : ℂ → Prop}
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (data : BoundedTypeSatelliteCertificate isBoundedTypeSatellite c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  localConnectivity_of_literatureMLCData data

/-- Dudko--Lyubich Feigenbaum certificate. -/
abbrev FeigenbaumCertificate
    (isFeigenbaum : ℂ → Prop)
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) :=
  LiteratureMLCData isFeigenbaum c hc

theorem localConnectivity_of_feigenbaumCertificate
    {isFeigenbaum : ℂ → Prop}
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (data : FeigenbaumCertificate isFeigenbaum c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  localConnectivity_of_literatureMLCData data

/-- Kahn--Kapiamba--Lyubich parabolically bounded primitive certificate. -/
abbrev ParabolicallyBoundedPrimitiveCertificate
    (isParabolicallyBoundedPrimitive : ℂ → Prop)
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) :=
  LiteratureMLCData isParabolicallyBoundedPrimitive c hc

theorem localConnectivity_of_parabolicallyBoundedPrimitiveCertificate
    {isParabolicallyBoundedPrimitive : ℂ → Prop}
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (data :
      ParabolicallyBoundedPrimitiveCertificate
        isParabolicallyBoundedPrimitive c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  localConnectivity_of_literatureMLCData data

/-- Neutral-renormalization certificate for a future pointwise MLC theorem.
The source key and puzzle data are explicit; neutral rigidity and bubble
estimates must be inserted by the analytic formalization. -/
abbrev NeutralRenormalizationCertificate
    (isNeutralRenormalizable : ℂ → Prop)
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) :=
  LiteratureMLCData isNeutralRenormalizable c hc

theorem localConnectivity_of_neutralRenormalizationCertificate
    {isNeutralRenormalizable : ℂ → Prop}
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (data :
      NeutralRenormalizationCertificate isNeutralRenormalizable c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  localConnectivity_of_literatureMLCData data

end

end Literature
end MLC
