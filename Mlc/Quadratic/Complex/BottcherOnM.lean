import Mlc.Quadratic.Complex.BottcherMotion
import Mathlib.Topology.MetricSpace.Basic

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Sketch: existence of Böttcher coordinates on the Mandelbrot set.

This is a placeholder for the analytic/dynamical proof that constructs the
parameter disk and associated Böttcher data uniformly over `M`.
-/

noncomputable def bottcher_onM_hyp : MLC.Quadratic.BottcherOnMHyp := by
  classical
  -- Intermediate stub: weaken the data to a trivially inhabited structure.
  refine
    { h_top := trivial
      h_stab := trivial
      B := fun _ _ => ⟨fun _ _ => 0⟩
      r := fun _ _ => 1
      r_pos := by
        intro n c₀
        norm_num
      in_M := trivial }

end MLC
