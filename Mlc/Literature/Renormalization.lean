import Mlc.Literature.PhaseParameter
import Mlc.MoleculeToParameterShrink

/-!
# Renormalization-facing MLC contracts

This module connects the existing satellite renormalization and principal-nest
developments to the literature-facing pointwise MLC target.  The analytic
renormalization bounds remain hypotheses; the topological and modulus
implications are proved.
-/

namespace MLC
namespace Literature

open Filter Set Topology

noncomputable section

/-- A satellite renormalization certificate carrying the uniform principal
nest modulus estimate used by the Lyubich/Dudko route. -/
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
