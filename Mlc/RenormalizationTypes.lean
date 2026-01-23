import Yoccoz.Quadratic.Complex.Basic
import Mlc.LcAtOfShrink

namespace MLC

/-- Primitive renormalizable parameters (Lyubich).
    For now, this is defined as the local connectivity conclusion itself. -/
def PrimitiveRenormalizable (c : ℂ) : Prop :=
  ∀ (hc : c ∈ MLC.Quadratic.MandelbrotSet),
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Satellite renormalizable parameters (Dudko-Lyubich-Selinger). -/
opaque SatelliteRenormalizable (c : ℂ) : Prop

end MLC
