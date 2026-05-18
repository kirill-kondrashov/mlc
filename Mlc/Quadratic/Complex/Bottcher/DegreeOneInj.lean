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

/-- If every fiber of a map has cardinality one, then the map is injective.

This is the final purely set-theoretic step in the degree-one covering
argument: once the topological/winding calculation has shown that every sheet
fiber has one point, no topology remains. -/
lemma injective_of_forall_natCard_fiber_eq_one
    {X Y : Type*} (f : X → Y)
    (hcard : ∀ y : Y, Nat.card ({x : X // f x = y}) = 1) :
    Function.Injective f := by
  intro x x' hxx'
  have hsub :
      Subsingleton ({z : X // f z = f x}) :=
    (Nat.card_eq_one_iff_unique.mp (hcard (f x))).1
  have hx_eq :
      (⟨x, rfl⟩ : {z : X // f z = f x}) =
        ⟨x', hxx'.symm⟩ :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val hx_eq

/-- Fiber cardinality of the restricted outside-open Böttcher map at `c = 2`. -/
noncomputable def RestrictedFiberCardTwo (y : {w : ℂ // 1 < ‖w‖}) : ℕ :=
  Nat.card
    ({x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} //
        MLC.bottcher_map_outside_open_to_exterior (2 : ℂ) x = y})

/-- The restricted outside-open Böttcher map at `c = 2` has one-point fibers.

This is the formal target of the covering-degree/winding-number calculation:
proper local-homeomorphy supplies a finite constant covering degree, and the
asymptotic winding computation identifies that degree as `1`. -/
def RestrictedDegreeOneFibersTwo : Prop :=
  ∀ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1

/-- The finite-sheeted covering degree is independent of the base point. This
is the formal counterpart of the covering-space part of the proof. -/
def RestrictedCoveringDegreeConstantTwo : Prop :=
  ∀ y y' : {w : ℂ // 1 < ‖w‖},
    RestrictedFiberCardTwo y = RestrictedFiberCardTwo y'

/-- The asymptotic winding calculation identifies the restricted covering
degree as one. Since the degree is constant, it is enough to record one fiber
with cardinality one. -/
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1

/-- Combining constant covering degree with the winding-number degree-one
calculation gives one-point fibers over every exterior point. -/
theorem restricted_degree_one_fibers_two_of_constant_of_winding
    (hconst : RestrictedCoveringDegreeConstantTwo)
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    RestrictedDegreeOneFibersTwo := by
  intro y
  rcases hwinding with ⟨y0, hy0⟩
  calc
    RestrictedFiberCardTwo y = RestrictedFiberCardTwo y0 := hconst y y0
    _ = 1 := hy0

/-- If the restricted outside-open map has degree-one fibers, then the original
Böttcher map is injective on the outside-open domain. -/
theorem injOn_outside_open_two_of_restricted_degree_one_fibers
    (hdegree : RestrictedDegreeOneFibersTwo) :
    Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  let f := MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)
  have hf_inj : Function.Injective f :=
    injective_of_forall_natCard_fiber_eq_one f hdegree
  intro z hz z' hz' hzz'
  let x : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} := ⟨z, hz⟩
  let x' : {z : ℂ // ‖z‖ > ‖(2 : ℂ)‖ + 2} := ⟨z', hz'⟩
  have hx_image : f x = f x' := by
    apply Subtype.ext
    simpa [f, x, x', MLC.bottcher_map_outside_open_to_exterior] using hzz'
  exact congrArg Subtype.val (hf_inj hx_image)

/-- Outside-open injectivity from the two formal pieces of the degree-one proof:
constant covering degree and asymptotic winding degree one. -/
theorem injOn_outside_open_two_of_restricted_covering_degree_constant_of_winding
    (hconst : RestrictedCoveringDegreeConstantTwo)
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
      {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2} := by
  exact injOn_outside_open_two_of_restricted_degree_one_fibers
    (restricted_degree_one_fibers_two_of_constant_of_winding hconst hwinding)

/-- Proper local-homeomorphy gives exterior surjectivity, and the degree-one
fiber conclusion gives outside-open injectivity. Together they construct the
external-ray map package at `c = 2`. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_restricted_degree_one_fibers
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hdegree : RestrictedDegreeOneFibersTwo) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    MLC.external_ray_map_data_of_injOn_outside_open_of_surj_exterior (2 : ℂ)
      (injOn_outside_open_two_of_restricted_degree_one_fibers hdegree)
      (MLC.bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
        (MLC.isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ)
          h_proper)
        h_local)

/-- External-ray map data from proper local-homeomorphy plus the two formal
pieces of the degree-one proof: constant covering degree and asymptotic winding
degree one. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_covering_degree_constant_of_winding
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (hconst : RestrictedCoveringDegreeConstantTwo)
    (hwinding : RestrictedAsymptoticWindingDegreeOneTwo) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_restricted_degree_one_fibers
      h_proper h_local
      (restricted_degree_one_fibers_two_of_constant_of_winding hconst hwinding)

/-- Proper local-homeomorphy of the restricted outside-open map already gives
exterior surjectivity via the clopen-image argument. -/
theorem bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))) :
    MLC.BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ) := by
  exact
    MLC.bottcherSurjOnExteriorFromOutsideOpen_two_of_isClosedRange_restrict_of_isLocalHomeomorph_restrict
      (MLC.isClosed_range_bottcher_map_outside_open_to_exterior_of_isProperMap (2 : ℂ) h_proper)
      h_local

/-- Direct proper/local restricted-map route at `c = 2`: once outside-open
injectivity is available, proper local-homeomorphy supplies the missing
exterior surjectivity and therefore closes the full external-ray package.

This integrates the surjectivity half of the degree-one proof non-circularly.
The remaining missing ingredient for the full route is now exactly the
outside-open injectivity theorem. -/
theorem external_ray_map_exists_two_of_proper_localHomeomorph_restrict_of_injOn
    (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_inj :
      Set.InjOn (MLC.Quadratic.bottcher_map (2 : ℂ))
        {z : ℂ | ‖z‖ > ‖(2 : ℂ)‖ + 2}) :
    MLC.Quadratic.ExternalRayMapData (2 : ℂ) := by
  exact
    MLC.external_ray_map_data_of_injOn_outside_open_of_surj_exterior (2 : ℂ) h_inj
      (bottcherSurjOnExteriorFromOutsideOpen_two_of_isProperMap_restrict_of_isLocalHomeomorph_restrict
        h_proper h_local)

end Mlc.Bottcher.DegreeOne
