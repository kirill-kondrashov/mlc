/-!
# Parameters of the checked grid

`gridFuel` is the number of subdivisions below the root squares of side `1/8`.
The search program `scripts/grid_hints.lean` found the certificates for these
parameters with inside certificates of periods up to 8 and at most 640 model
steps; the kernel checks every certificate and does not use these limits.
-/

namespace MLC.Certified

/-- Number of subdivisions below the root squares of side `1/8`. -/
def gridFuel : Nat := 6

/-- Depth of the finest cells, `3 + gridFuel`. -/
def gridDepth : Nat := 3 + gridFuel

end MLC.Certified
