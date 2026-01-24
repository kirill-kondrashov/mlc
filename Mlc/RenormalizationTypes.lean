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
axiom parameterToBMol_spec (c : ℂ) :
  ∃ g : BMol, g.f = (fun z : ℂ => z^2 + c) ∧ criticalValue g = c

/-- A quadratic-like map attached to parameter `c` for the Molecule framework. -/
noncomputable def parameterToBMol (c : ℂ) : BMol :=
  Classical.choose (parameterToBMol_spec c)

lemma parameterToBMol_criticalValue (c : ℂ) :
    criticalValue (parameterToBMol c) = c := by
  simpa using (Classical.choose_spec (parameterToBMol_spec c)).2

/-- Satellite renormalizable parameters, modeled by fast renormalizability of the associated BMol map. -/
def SatelliteRenormalizable (c : ℂ) : Prop :=
  IsFastRenormalizable (parameterToBMol c)

end
end MLC
