/-!
# Parameters of the checked grid

`gridFuel` is the number of subdivisions below the root squares of side `1/8`.
The search program `scripts/grid_hints.lean` found the certificates with inside
certificates of periods up to 8; the kernel checks every certificate and does not
use the limits of the search. Each refinement of the grid (`scripts/refine_grid.py`)
raises `gridFuel` by one.
-/

namespace MLC.Certified

/-- Number of subdivisions below the root squares of side `1/8`. -/
def gridFuel : Nat := 8

/-- Depth of the finest cells, `3 + gridFuel`. -/
def gridDepth : Nat := 3 + gridFuel

end MLC.Certified
