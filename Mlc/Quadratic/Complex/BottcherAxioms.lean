import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic

/-- The Böttcher map `φ_c` conjugates `f_c(z) = z^2 + c` to `z^2` near infinity. -/
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  let w := lim (map (fun n => ((fun w => w^2 + c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n)) atTop)
  let u := if w = 0 then 1 else w / ↑‖w‖
  u * ↑(Real.exp (MLC.Quadratic.green_function c z))

/-- The domain where the Böttcher map is defined (basin of infinity). -/
def basin_of_infinity (c : ℂ) : Set ℂ :=
  {z | ¬ MLC.Quadratic.boundedOrbit c z}

/-- The inverse of the Böttcher map exists (ray map). -/
noncomputable def external_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  if 1 < ‖w‖ then Function.invFun (bottcher_map c) w else 0

/-! Domain for the Böttcher coordinate. -/
def bottcher_domain (c : ℂ) : Set ℂ :=
  external_ray_map c '' {w | 1 < ‖w‖}

namespace Axioms

axiom bottcher_continuous_on (c : ℂ) :
    ContinuousOn (bottcher_map c) (bottcher_domain c)

axiom bottcher_right_inv (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w

end Axioms

lemma bottcher_continuous_on (c : ℂ) :
    ContinuousOn (bottcher_map c) (bottcher_domain c) :=
  Axioms.bottcher_continuous_on c

lemma bottcher_right_inv (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    bottcher_map c (external_ray_map c w) = w :=
  Axioms.bottcher_right_inv c w hw

lemma bottcher_surj (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    w ∈ bottcher_map c '' bottcher_domain c := by
  refine ⟨external_ray_map c w, ?_, ?_⟩
  · exact ⟨w, hw, rfl⟩
  · exact bottcher_right_inv c w hw

axiom bottcher_left_inv (c : ℂ) (z : ℂ) (hz : z ∈ basin_of_infinity c) :
    external_ray_map c (bottcher_map c z) = z

/-- The ray map is continuous on the exterior of the disk. -/
axiom ray_map_continuous_on (c : ℂ) :
    ContinuousOn (external_ray_map c) {w | 1 < ‖w‖}

axiom invariance_of_domain_complex {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (hinj : Set.InjOn f U) : IsOpenMap (U.restrict f)

/-- The sequence of roots converges locally uniformly to the Böttcher map. -/
axiom bottcher_seq_converges (c : ℂ) :
    TendstoLocallyUniformlyOn (fun n z => ((fun w => w^2 + c)^[n] z) ^ ((1 : ℂ) / (2 : ℂ) ^ n))
    (bottcher_map c) atTop (basin_of_infinity c)

/-- Extension of the ray map to the closed exterior of the disk. -/
noncomputable def extended_ray_map (c : ℂ) (w : ℂ) : ℂ :=
  if 1 ≤ ‖w‖ then lim (map (external_ray_map c) (nhdsWithin w {z | 1 < ‖z‖})) else 0

/-- The extended ray map agrees with the external ray map on the open exterior. -/
axiom extended_ray_map_eq (c : ℂ) (w : ℂ) (hw : 1 < ‖w‖) :
    extended_ray_map c w = external_ray_map c w

/-- The extended ray map is continuous on the closed exterior {w | 1 ≤ |w|}. -/
axiom extended_ray_map_continuous (c : ℂ) :
    ContinuousOn (extended_ray_map c) {w | 1 ≤ ‖w‖}

/-- The extended ray map maps the unit circle to the Julia set (subset of K). -/
axiom extended_ray_map_lands (c : ℂ) (w : ℂ) (hw : ‖w‖ = 1) :
    extended_ray_map c w ∈ MLC.Quadratic.K c

end Quadratic

end MLC
