/-
# Renormalization Tower Existence

The existence of at least one infinitely renormalizable parameter.
This is a standard result in complex dynamics (e.g., the Feigenbaum point c ≈ -1.40115...).

Rather than using the hard axiom `ir_locally_connected_seam` (which concludes that IR parameters
are locally connected on the seam boundary), we use the much weaker and more standard fact that
there exist infinitely renormalizable parameters whose renormalization towers exist.

The Feigenbaum parameter is known to be infinitely renormalizable, and its renormalization tower
is well-defined. This axiom asserts the existence of such a parameter and its tower.
-/

import Mlc.MoleculeRenormalizationTower
import Mlc.RenormalizationTypes

namespace MLC

open Quadratic Complex

noncomputable section

/-- The existence of at least one infinitely renormalizable parameter with a renormalization tower.
    This is justified by the existence of the Feigenbaum point or any other infinitely
    renormalizable parameter in the Mandelbrot set. -/
axiom exists_renormalization_tower : ∃ (c : ℂ), Nonempty (RenormalizationTower (parameterToBMol c))

end

end MLC
