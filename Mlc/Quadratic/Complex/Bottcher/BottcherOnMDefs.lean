import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Basic

namespace MLC

open Complex Topology Set Filter

/-- The quadratic polynomial with parameter `c`. -/
def quadratic_map (c : ℂ) (z : ℂ) : ℂ :=
  z ^ 2 + c

/-- Points whose quadratic orbit escapes to infinity in norm. -/
def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop}

end MLC
