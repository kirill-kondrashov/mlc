import Mlc.Quadratic.Complex.BottcherAxioms

namespace MLC

open Quadratic Complex Topology Set Filter

def quadratic_map (c : ℂ) (z : ℂ) : ℂ :=
  z ^ 2 + c

def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop}

def outside_disk (c : ℂ) : Set ℂ :=
  {z | ‖z‖ ≥ ‖c‖ + 2}

end MLC
