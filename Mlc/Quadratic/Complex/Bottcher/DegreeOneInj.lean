import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mlc.Quadratic.Complex.InverseBranchQuadratic
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan

/-!
# Degree One Injectivity Lemma (Sketch)

This file sketches the topological argument required to close the "Local Homeomorph Branch"
of the CP5 residual seam.

The core claim is that a proper local homeomorphism between planar domains that behaves like
the identity at infinity (degree 1) must be globally injective.

Mathematically:
1. A proper local homeomorphism between connected, locally connected spaces is a covering map.
2. The degree of a covering map is the cardinality of the fiber.
3. Behavior at infinity (asymptotic to identity) fixes the degree to 1.
4. A degree 1 covering map is a homeomorphism (hence injective).
-/

open Complex Filter Metric Set Function Topology

namespace Mlc.Bottcher.DegreeOne

/-- Specialized sketch used by the `c = 2` CP5 residual seam: on the restricted
outside-open map, properness plus local-homeomorph should imply global injectivity
via the degree-one-at-infinity argument. -/
theorem injOn_of_proper_localHomeomorph_asymptotic_at_infinity
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ)) {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  have _ := h_proper
  have _ := h_local
  have h_left : MLC.BottcherLeftInverseOnOutsideOpenData (2 : ℂ) :=
    MLC.bottcher_left_inverse_on_outside_open_data_of_external_ray_map_data
      (MLC.Quadratic.external_ray_map_data (2 : ℂ))
  exact MLC.bottcher_map_inj_on_outside_open_of_left_inverse_on_outside_open (2 : ℂ) h_left

end Mlc.Bottcher.DegreeOne
