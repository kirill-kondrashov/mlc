import Mlc.Literature.PhaseParameter
import Mlc.MoleculeToParameterShrink

/-!
# Renormalization-facing MLC contracts

This module preserves the legacy satellite/principal-nest implications.
`Literature.ModelAudit` proves that their weighted-area lower-bound input
cannot exist. Genuine conformal-modulus bounds and graph-cut parameter
pieces require a separate construction.
-/

namespace MLC
namespace Literature

open Filter Set Topology

noncomputable section

/-- A legacy frozen-model certificate. Its lower-bound field is refuted in
`Literature.ModelAudit`; it is not a certificate for a published theorem. -/
structure SatelliteAPrioriCertificate (c : ℂ) where
  tower : SatelliteRenormalizableTower c
  uniformBound :
    PrincipalNestTarget.UniformConformalLowerBoundTarget c tower

theorem satelliteCertificate_gives_parameter_shrink
    {c : ℂ} (certificate : SatelliteAPrioriCertificate c) :
    (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c} :=
  PrincipalNestTarget.paraPuzzle_shrink_of_uniformConformalLowerBoundTarget
    c certificate.tower certificate.uniformBound

/-- The complete pointwise MLC implication after the connected parapuzzle
pieces have been supplied. -/
theorem localConnectivity_of_satelliteAPrioriCertificate
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (certificate : SatelliteAPrioriCertificate c)
    (connected :
      ∀ n, IsConnected
        (MLC.Quadratic.ParaPuzzlePieceAt c n ∩ reviewMandelbrotSet)) :
    MandelbrotLocallyConnectedAt c hc := by
  exact MLC.preconnected_nhds_of_shrink_of_connected_at c hc connected
    (satelliteCertificate_gives_parameter_shrink certificate)

/-- The source-level theorem interface used by the newer primitive and
neutral-renormalization papers. -/
structure RenormalizationLiteratureCertificate (classPredicate : ℂ → Prop) where
  result : PointwiseMLCResult classPredicate
  source_key : String

end

end Literature
end MLC
