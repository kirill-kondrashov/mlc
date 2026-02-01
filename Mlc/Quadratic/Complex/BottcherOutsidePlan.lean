import Mlc.Quadratic.Complex.BottcherOutsideOutline

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
Plan: eliminate `bottcher_map_inj_on_outside`.

Step 1: Analyticity on the exterior.
  Goal: `AnalyticOnNhd ℂ (bottcher_map c) {‖z‖ > ‖c‖ + 2}`.
  Requires: `outside_disk` (or the open exterior) is contained in `slit_orbit c`.

Step 2: Normalization at infinity.
  Goal: `Tendsto (fun z => bottcher_map c z / z) atInfinity (𝓝 1)`.
  Use: the root sequence, branch coherence on slit, and escape estimates.

Step 3: Derivative nonvanishing on the exterior.
  Goal: `deriv (bottcher_map c) z ≠ 0` on `outside_disk c`.
  Use: analytic order lemma + local injectivity from Step 2.

Step 4: Properness / degree-one argument.
  Goal: global injectivity on `outside_disk c`.
  Use: local injectivity + properness.

Once Steps 1–4 are formalized, remove the axiom
`bottcher_map_inj_on_outside`.
-/

lemma bottcher_map_analytic_on_outside
    (c : ℂ) (hslit : {z : ℂ | ‖z‖ > ‖c‖ + 2} ⊆ slit_orbit c) :
    AnalyticOnNhd ℂ (Quadratic.bottcher_map c) {z : ℂ | ‖z‖ > ‖c‖ + 2} :=
  bottcher_map_analytic_on_outside_of_slit c hslit

end MLC
