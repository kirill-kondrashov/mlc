import Yoccoz.Quadratic.Complex.Basic
import Mlc.LcAtOfShrink
import Molecule.Rfast

namespace MLC

open Molecule

noncomputable section

/-- Primitive renormalizable parameters (Lyubich).
    For now, this is defined as the local connectivity conclusion itself. -/
def PrimitiveRenormalizable (c : ℂ) : Prop :=
  ∀ (hc : c ∈ MLC.Quadratic.MandelbrotSet),
    MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩

/-- Satellite renormalizable parameters (Dudko-Lyubich-Selinger). -/
opaque parameterToBMol : ℂ → BMol

/-- Satellite renormalizable parameters, modeled by fast renormalizability of the associated BMol map. -/
def SatelliteRenormalizable (c : ℂ) : Prop :=
  IsFastRenormalizable (parameterToBMol c)

end
end MLC
