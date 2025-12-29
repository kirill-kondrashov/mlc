import Mlc.Quadratic.Complex.Basic
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic Complex Topology

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/
theorem MLC_Conjecture : LocallyConnectedSpace MandelbrotSet := sorry

end MLC
