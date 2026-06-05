import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory

namespace MLC

open Quadratic Set

/-!
Preimage-of-exterior lemma needed to eliminate `MLC.proxy_bottcher_map_inj_on_outside`.

Sketch of the missing dynamical input:
* Show `basin_of_infinity c ⊆ outside_disk c`.
* One route: use quantitative Green function bounds (or escape estimates)
  to prove that if `z` escapes, then eventually `‖z‖ ≥ ‖c‖ + 2`, and then
  use forward invariance to pull back to `z`.
* With that, any `z` with `‖Quadratic.proxy_bottcher_map c z‖ > 1` for the current proxy
  lies in the basin (already proved),
  hence in `outside_disk c`.
-/

lemma proxy_bottcher_map_preimage_exterior_subset_outside
    (c : ℂ)
    (hbasin : ∀ z, z ∈ Quadratic.basin_of_infinity c → z ∈ outside_disk c) :
    (Quadratic.proxy_bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c := by
  intro z hz
  have hz' : 1 < ‖Quadratic.proxy_bottcher_map c z‖ := by
    simpa [Set.preimage] using hz
  have hz_basin : z ∈ Quadratic.basin_of_infinity c :=
    proxy_bottcher_map_norm_gt_one_implies_basin c (z := z) hz'
  exact hbasin z hz_basin

end MLC
