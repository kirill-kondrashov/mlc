import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.PathConnected
import Mlc.GreenSublevelConnectedDirect

namespace MLC

open Quadratic Complex Topology Set Filter

/-- For c ∈ M, the filled Julia set K_c is connected. -/
lemma Kc_connected (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) : IsConnected (MLC.Quadratic.K c) := by
  exact MLC.Quadratic.filled_julia_set_connected hc

/-- The Green function is continuous on ℂ. -/
lemma green_continuous (c : ℂ) : Continuous (MLC.Quadratic.green_function c) := by
  exact MLC.Quadratic.continuous_green_function c

/--
For `c ∈ M` the Green sublevel sets `{z | G_c(z) < ε}` are connected.

Discharged directly by the potential-theory argument of `green_sublevel_connected_direct`
(Route A: `G_c` is harmonic on the basin, so a minimum principle forces every connected
component of the sublevel set to meet `K_c`). The former route through
`green_sublevel_joined_to_Kc` — which depended on the unsound axioms
`extended_ray_map_free_continuous` and `green_function_strictMono_along_ray_basin_seam` —
is no longer used.
-/
lemma green_sublevel_connected_of_connected_Kc (c : ℂ) (n : ℕ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) :
    IsConnected (MLC.Quadratic.GreenSublevel c n) :=
  green_sublevel_connected_direct c n hc

/--
Theorem: Green sublevel sets are connected on the Mandelbrot set.
(Formerly an axiom.)
-/
theorem green_sublevel_connected_onM :
    MLC.Quadratic.GreenSublevelConnectedHyp := {
  connected := fun c n hc => green_sublevel_connected_of_connected_Kc c n hc
}

/--
Theorem: Green sublevel sets are connected on the Mandelbrot set.
(Formerly an axiom.)
-/
theorem green_sublevel_connected : MLC.Quadratic.GreenSublevelConnectedHyp :=
  green_sublevel_connected_onM

end MLC
