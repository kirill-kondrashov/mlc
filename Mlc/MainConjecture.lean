import Mlc.Quadratic.Complex.Basic
import Mathlib.Topology.Connected.LocallyConnected

namespace MLC

open Quadratic Complex Topology

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected.

Reference: "Conformal Geometry and Dynamics of Quadratic Polynomials",
https://indico.ictp.it/event/a12182/session/2/contribution/1/material/0/0.pdf
(See Section 21.1, p. 123 for the statement of the MLC conjecture)
-/
theorem MLC_Conjecture : LocallyConnectedSpace MandelbrotSet := sorry

end MLC
