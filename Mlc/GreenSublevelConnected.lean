import Mlc.Quadratic.Complex.GreenSublevel
import Mlc.GreenSublevelConnectedDirect

namespace MLC

open Quadratic Complex Topology Set Filter

/--
Theorem: Green sublevel sets are connected on the Mandelbrot set.
(Formerly an axiom.)
-/
theorem green_sublevel_connected_onM :
    MLC.Quadratic.GreenSublevelConnectedHyp := {
  connected := fun c n hc => green_sublevel_connected_direct c n hc
}

end MLC
