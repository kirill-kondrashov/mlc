/-!
# Parameters of the checked grid

`gridPmax` is the largest period scanned by the trapping test, `gridJ` the
number of critical-orbit steps before it, and `gridFuel` the number of
subdivisions below the root squares of side `1/8`.
-/

namespace MLC.Certified

/-- Maximal period scanned by the trapping test. -/
def gridPmax : Nat := 4

/-- Number of critical-orbit steps before the trapping test. -/
def gridJ : Nat := 20

/-- Number of subdivisions below the root squares of side `1/8`. -/
def gridFuel : Nat := 5

/-- Depth of the finest cells, `3 + gridFuel`. -/
def gridDepth : Nat := 3 + gridFuel

end MLC.Certified
