import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory

namespace MLC
namespace Quadratic

open Topology Set Filter

/-- Data for a local inverse branch of the Böttcher map near `z` on the slit-orbit. -/
structure LocalInverseAt (c : ℂ) (z : ℂ) where
  (U : Set ℂ)
  (hUopen : IsOpen U)
  (hUslit : U ⊆ slit_orbit c)
  (hUbasin : U ⊆ basin_of_infinity c)
  (hz : z ∈ U)
  (hderiv : deriv (proxy_bottcher_map c) z ≠ 0)

/-- The associated local inverse map from `LocalInverseAt`. -/
noncomputable def local_inverse_at {c : ℂ} {z : ℂ}
    (h : LocalInverseAt c z) : ℂ → ℂ :=
  external_ray_map_local c h.U h.hUopen h.hUslit h.hUbasin z h.hz h.hderiv

/-- Local right-inverse property near `proxy_bottcher_map c z`. -/
lemma local_inverse_right_inverse
    {c : ℂ} {z : ℂ} (h : LocalInverseAt c z) :
    ∀ᶠ y in 𝓝 (proxy_bottcher_map c z),
      proxy_bottcher_map c (local_inverse_at h y) = y := by
  simpa [local_inverse_at] using
    (external_ray_map_local_right_inverse c h.U h.hUopen h.hUslit h.hUbasin z h.hz h.hderiv)

/-- Local left-inverse property near `z`. -/
lemma local_inverse_left_inverse
    {c : ℂ} {z : ℂ} (h : LocalInverseAt c z) :
    ∀ᶠ x in 𝓝 z,
      local_inverse_at h (proxy_bottcher_map c x) = x := by
  simpa [local_inverse_at] using
    (external_ray_map_local_left_inverse c h.U h.hUopen h.hUslit h.hUbasin z h.hz h.hderiv)

/-!
A hypothesis: every slit-orbit basin point admits a local inverse branch.
This is the minimal local input needed to attempt a global inverse-branch
construction along slit orbits.
-/
def SlitInverseAtlas (c : ℂ) : Prop :=
  ∀ z, z ∈ slit_orbit c ∩ basin_of_infinity c → ∃ _h : LocalInverseAt c z, True

def eventually_slit_orbit (c : ℂ) (z : ℂ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (quadratic_map c)^[n] z ∈ Complex.slitPlane

def eventual_slit_set (c : ℂ) : Set ℂ := {z | eventually_slit_orbit c z}

lemma outside_eventually_slit_orbit (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2) :
    eventually_slit_orbit c z :=
  bottcher_outside_axiom c z hz

def EventualSlitImpliesSlitOrbit (c : ℂ) : Prop :=
  ∀ z, eventually_slit_orbit c z → z ∈ slit_orbit c

lemma outside_in_slit_orbit_of_eventual
    (c z : ℂ) (hz : ‖z‖ > ‖c‖ + 2)
    (himp : EventualSlitImpliesSlitOrbit c) :
    z ∈ slit_orbit c :=
  himp z (outside_eventually_slit_orbit c z hz)

/-!
Partial global inverse on the *eventual* slit orbit.

This is weaker than a global inverse on `slit_orbit`, but it is the natural
target of `bottcher_outside_axiom`.
-/

def EventualSlitInverseAtlas (c : ℂ) : Prop :=
  ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c → ∃ _h : LocalInverseAt c z, True

def EventualSlitInverseCompatible {c : ℂ} (hA : EventualSlitInverseAtlas c) : Prop :=
  ∀ z w
    (hz : z ∈ eventual_slit_set c ∩ basin_of_infinity c)
    (hw : w ∈ eventual_slit_set c ∩ basin_of_infinity c),
      ∀ᶠ y in 𝓝 (proxy_bottcher_map c z) ⊓ 𝓝 (proxy_bottcher_map c w),
        local_inverse_at (Classical.choose (hA z hz)) y =
          local_inverse_at (Classical.choose (hA w hw)) y

def GlobalInverseOnEventualSlit (c : ℂ) (hA : EventualSlitInverseAtlas c) : Prop :=
  ∃ g : ℂ → ℂ,
    (∀ z (hz : z ∈ eventual_slit_set c ∩ basin_of_infinity c),
      ∀ᶠ y in 𝓝 (proxy_bottcher_map c z),
        g y = local_inverse_at (Classical.choose (hA z hz)) y) ∧
    (∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
      ∀ᶠ x in 𝓝 z, g (proxy_bottcher_map c x) = x)

def EventualSlitInverseGluing (c : ℂ) : Prop :=
  ∀ hA : EventualSlitInverseAtlas c,
    EventualSlitInverseCompatible hA → GlobalInverseOnEventualSlit c hA

lemma global_inverse_on_eventual_slit_of_gluing
    {c : ℂ} (hA : EventualSlitInverseAtlas c)
    (hcompat : EventualSlitInverseCompatible hA) (hglue : EventualSlitInverseGluing c) :
    GlobalInverseOnEventualSlit c hA :=
  hglue hA hcompat

/-!
Compatibility can follow from a local uniqueness principle: if two local
inverses are left inverses near the same point, they agree near the image.
We record this as a hypothesis for future use.
-/

def EventualSlitLocalUniqueness (c : ℂ) : Prop :=
  ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
    ∀ h₁ h₂ : LocalInverseAt c z,
      (∀ᶠ x in 𝓝 z, local_inverse_at h₁ (proxy_bottcher_map c x) = x) →
      (∀ᶠ x in 𝓝 z, local_inverse_at h₂ (proxy_bottcher_map c x) = x) →
        ∀ᶠ y in 𝓝 (proxy_bottcher_map c z), local_inverse_at h₁ y = local_inverse_at h₂ y

def EventualSlitOverlapHyp (c : ℂ) : Prop :=
  ∀ z w, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
    w ∈ eventual_slit_set c ∩ basin_of_infinity c →
      Filter.NeBot (𝓝 (proxy_bottcher_map c z) ⊓ 𝓝 (proxy_bottcher_map c w))

def EventualSlitCompatibilityFromOverlap (c : ℂ) : Prop :=
  ∀ hA : EventualSlitInverseAtlas c,
    EventualSlitLocalUniqueness c →
      EventualSlitOverlapHyp c → EventualSlitInverseCompatible hA

lemma eventual_slit_inverse_compatible_of_overlap
    (c : ℂ) (hA : EventualSlitInverseAtlas c)
    (huniq : EventualSlitLocalUniqueness c) (hover : EventualSlitOverlapHyp c)
    (hcomp : EventualSlitCompatibilityFromOverlap c) :
    EventualSlitInverseCompatible hA :=
  hcomp hA huniq hover

def EventualSlitInverseGluingWithUniqueness (c : ℂ) : Prop :=
  ∀ hA : EventualSlitInverseAtlas c,
    EventualSlitLocalUniqueness c →
      EventualSlitInverseCompatible hA → GlobalInverseOnEventualSlit c hA

lemma global_inverse_on_eventual_slit_of_gluing_with_uniqueness
    {c : ℂ} (hA : EventualSlitInverseAtlas c)
    (huniq : EventualSlitLocalUniqueness c)
    (hcompat : EventualSlitInverseCompatible hA)
    (hglue : EventualSlitInverseGluingWithUniqueness c) :
    GlobalInverseOnEventualSlit c hA :=
  hglue hA huniq hcompat

/-!
Local inverse existence on the eventual slit orbit requires a nonvanishing
derivative hypothesis at the point. We record this as a helper for building
an `EventualSlitInverseAtlas` once such nondegeneracy is available.
-/

def EventualSlitNonzeroDeriv (c : ℂ) : Prop :=
  ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      U ⊆ slit_orbit c ∧ U ⊆ basin_of_infinity c ∧
      deriv (proxy_bottcher_map c) z ≠ 0

def EventualSlitOpenNeighborhood (c : ℂ) : Prop :=
  ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      U ⊆ slit_orbit c ∧ U ⊆ basin_of_infinity c

def EventualSlitDerivNonzero (c : ℂ) : Prop :=
  ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
    deriv (proxy_bottcher_map c) z ≠ 0

def EventualSlitNonzeroDerivHyp (c : ℂ) : Prop :=
  EventualSlitOpenNeighborhood c ∧ EventualSlitDerivNonzero c

lemma eventual_slit_nonzero_deriv_of_open
    (c : ℂ) (hopen : EventualSlitOpenNeighborhood c)
    (hder : EventualSlitDerivNonzero c) :
    EventualSlitNonzeroDeriv c := by
  intro z hz
  rcases hopen z hz with ⟨U, hUopen, hzU, hUslit, hUbasin⟩
  exact ⟨U, hUopen, hzU, hUslit, hUbasin, hder z hz⟩

lemma eventual_slit_nonzero_deriv_of_hyp
    (c : ℂ) (h : EventualSlitNonzeroDerivHyp c) :
    EventualSlitNonzeroDeriv c :=
  eventual_slit_nonzero_deriv_of_open c h.1 h.2

lemma local_inverse_at_of_eventual_slit
    (c : ℂ) (hderiv : EventualSlitNonzeroDeriv c) :
    ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
      ∃ _h : LocalInverseAt c z, True := by
  intro z hz
  rcases hderiv z hz with ⟨U, hUopen, hzU, hUslit, hUbasin, hder⟩
  refine ⟨{ U := U
           , hUopen := hUopen
           , hUslit := hUslit
           , hUbasin := hUbasin
           , hz := hzU
           , hderiv := hder }, trivial⟩

lemma eventual_slit_inverse_atlas_of_nonzero_deriv
    (c : ℂ) (hderiv : EventualSlitNonzeroDeriv c) :
    EventualSlitInverseAtlas c :=
  local_inverse_at_of_eventual_slit c hderiv

/-- Choose a local inverse at a slit-orbit basin point (noncomputably). -/
noncomputable def choose_local_inverse
    {c : ℂ} (hA : SlitInverseAtlas c) (z : ℂ)
    (hz : z ∈ slit_orbit c ∩ basin_of_infinity c) : LocalInverseAt c z :=
  Classical.choose (hA z hz)

lemma choose_local_inverse_left_inverse
    {c : ℂ} (hA : SlitInverseAtlas c) (z : ℂ)
    (hz : z ∈ slit_orbit c ∩ basin_of_infinity c) :
    ∀ᶠ x in 𝓝 z,
      local_inverse_at (choose_local_inverse hA z hz) (proxy_bottcher_map c x) = x := by
  simpa using
    (local_inverse_left_inverse (choose_local_inverse hA z hz))

/-!
Compatibility and gluing hypotheses for local inverse branches.

These are *interface* definitions used to state what is needed for a
global inverse branch on the slit-orbit basin.
-/

def SlitInverseCompatible {c : ℂ} (hA : SlitInverseAtlas c) : Prop :=
  ∀ z w
    (hz : z ∈ slit_orbit c ∩ basin_of_infinity c)
    (hw : w ∈ slit_orbit c ∩ basin_of_infinity c),
      ∀ᶠ y in 𝓝 (proxy_bottcher_map c z) ⊓ 𝓝 (proxy_bottcher_map c w),
        local_inverse_at (choose_local_inverse hA z hz) y =
          local_inverse_at (choose_local_inverse hA w hw) y

def GlobalInverseOnSlit (c : ℂ) (hA : SlitInverseAtlas c) : Prop :=
  ∃ g : ℂ → ℂ,
    (∀ z (hz : z ∈ slit_orbit c ∩ basin_of_infinity c),
      ∀ᶠ y in 𝓝 (proxy_bottcher_map c z),
        g y = local_inverse_at (choose_local_inverse hA z hz) y) ∧
    (∀ z, z ∈ slit_orbit c ∩ basin_of_infinity c →
      ∀ᶠ x in 𝓝 z, g (proxy_bottcher_map c x) = x)

lemma global_inverse_left_inverse_on_slit
    {c : ℂ} {hA : SlitInverseAtlas c}
    (hG : GlobalInverseOnSlit c hA) :
    ∀ z, z ∈ slit_orbit c ∩ basin_of_infinity c →
      ∀ᶠ x in 𝓝 z, (Classical.choose hG) (proxy_bottcher_map c x) = x := by
  have hleft := (Classical.choose_spec hG).2
  intro z hz
  simpa using (hleft z hz)

def SlitInverseGluing (c : ℂ) : Prop :=
  ∀ hA : SlitInverseAtlas c, SlitInverseCompatible hA → GlobalInverseOnSlit c hA

lemma global_inverse_on_slit_of_gluing
    {c : ℂ} (hA : SlitInverseAtlas c)
    (hcompat : SlitInverseCompatible hA) (hglue : SlitInverseGluing c) :
    GlobalInverseOnSlit c hA :=
  hglue hA hcompat

end Quadratic
end MLC
