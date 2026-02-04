import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic

namespace MLC

open Complex Topology Set Filter

def quadratic_map (c : ℂ) (z : ℂ) : ℂ :=
  z ^ 2 + c

def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop}

def outside_disk (c : ℂ) : Set ℂ :=
  basin_of_infinity c

end MLC
