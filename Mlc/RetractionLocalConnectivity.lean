import Mlc.CategoricalRoot
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local connectedness from a supplied retraction

A continuous retraction of a locally connected space has locally connected
target. In particular, a retraction of a convex subset of the parameter plane
onto the Mandelbrot set would imply MLC. No such retraction is constructed or
assumed to exist here.
-/

namespace MLC.UniformGeometry

open Set Topology

/-- A continuous map with a continuous right inverse preserves local
connectedness. No compactness or separation assumptions are needed. -/
theorem locallyConnectedSpace_of_continuous_retraction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] (i : Y → X) (r : X → Y)
    (hi : Continuous i) (hr : Continuous r) (hfix : Function.LeftInverse r i) :
    LocallyConnectedSpace Y := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro y U hU
  have hpre : r ⁻¹' U ∈ 𝓝 (i y) := by
    apply hr.continuousAt.preimage_mem_nhds
    simpa only [hfix y] using hU
  obtain ⟨W, hW, hconn, hWU⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp
      (inferInstance : LocallyConnectedSpace X) (i y) (r ⁻¹' U) hpre
  refine ⟨r '' W, ?_, hconn.image r hr.continuousOn, ?_⟩
  · apply Filter.mem_of_superset (hi.continuousAt.preimage_mem_nhds hW)
    intro z hz
    exact ⟨i z, hz, hfix z⟩
  · rintro z ⟨x, hx, rfl⟩
    exact hWU hx

/-- Subspace version with an ambient-valued retraction and explicit range and
pointwise fixing hypotheses. -/
theorem locallyConnectedSpace_of_subspace_retraction
    {X : Type*} [TopologicalSpace X] {S K : Set X}
    [LocallyConnectedSpace K] (hSK : S ⊆ K) (r : K → X)
    (hr : Continuous r) (hrange : ∀ x, r x ∈ S)
    (hfix : ∀ c (hc : c ∈ S), r ⟨c, hSK hc⟩ = c) :
    LocallyConnectedSpace S := by
  let i : S → K := fun c => ⟨c.1, hSK c.2⟩
  let rS : K → S := fun x => ⟨r x, hrange x⟩
  apply locallyConnectedSpace_of_continuous_retraction i rS
  · exact continuous_subtype_val.subtype_mk _
  · exact hr.subtype_mk _
  · intro c
    exact Subtype.ext (hfix c.1 c.2)

/-- Relative balls in a convex subset of a real normed space are connected. -/
theorem locallyConnectedSpace_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : Convex ℝ K) : LocallyConnectedSpace K := by
  apply locallyConnectedSpace_of_connected_bases
    (fun x ε => Metric.ball x ε) (fun _ ε => 0 < ε)
  · intro x
    exact Metric.nhds_basis_ball
  · intro x ε _
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_ball]
    exact ((convex_ball (x : E) ε).inter hK).isPreconnected

/-- A supplied retraction from any locally connected parameter domain implies
local connectedness of the Mandelbrot set. -/
theorem mandelbrot_locallyConnected_of_retraction_of_locallyConnected
    {K : Set ℂ} [LocallyConnectedSpace K]
    (hMK : MLC.mandelbrotSet ⊆ K) (r : K → ℂ)
    (hr : Continuous r) (hrange : ∀ x, r x ∈ MLC.mandelbrotSet)
    (hfix : ∀ c (hc : c ∈ MLC.mandelbrotSet), r ⟨c, hMK hc⟩ = c) :
    LocallyConnectedSpace MLC.mandelbrotSet :=
  locallyConnectedSpace_of_subspace_retraction hMK r hr hrange hfix

/-- A continuous retraction of a convex parameter domain onto the Mandelbrot
set implies MLC. Compactness of the domain is not required. -/
theorem mandelbrot_locallyConnected_of_retraction
    {K : Set ℂ} (hK : Convex ℝ K) (hMK : MLC.mandelbrotSet ⊆ K)
    (r : K → ℂ) (hr : Continuous r)
    (hrange : ∀ x, r x ∈ MLC.mandelbrotSet)
    (hfix : ∀ c (hc : c ∈ MLC.mandelbrotSet), r ⟨c, hMK hc⟩ = c) :
    LocallyConnectedSpace MLC.mandelbrotSet := by
  letI : LocallyConnectedSpace K := locallyConnectedSpace_of_convex hK
  exact mandelbrot_locallyConnected_of_retraction_of_locallyConnected
    hMK r hr hrange hfix

/-- Straight-line interpolation from the identity to an ambient-valued map. -/
noncomputable def straightLineDeformation {K : Set ℂ} (r : K → ℂ) :
    K × Set.Icc (0 : ℝ) 1 → ℂ :=
  fun p => (1 - p.2.1) • p.1.1 + p.2.1 • r p.1

theorem continuous_straightLineDeformation {K : Set ℂ} {r : K → ℂ}
    (hr : Continuous r) : Continuous (straightLineDeformation r) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
    (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul (hr.comp continuous_fst))

@[simp]
theorem straightLineDeformation_zero {K : Set ℂ} (r : K → ℂ) (x : K) :
    straightLineDeformation r (x, ⟨0, by norm_num⟩) = x.1 := by
  simp [straightLineDeformation]

@[simp]
theorem straightLineDeformation_one {K : Set ℂ} (r : K → ℂ) (x : K) :
    straightLineDeformation r (x, ⟨1, by norm_num⟩) = r x := by
  simp [straightLineDeformation]

theorem straightLineDeformation_fixed {K : Set ℂ} {r : K → ℂ}
    (x : K) (hx : r x = x.1) (t : Set.Icc (0 : ℝ) 1) :
    straightLineDeformation r (x, t) = x.1 := by
  change (1 - t.1) • x.1 + t.1 • r x = x.1
  rw [hx, ← add_smul, sub_add_cancel, one_smul]

theorem straightLineDeformation_mem {K : Set ℂ} (hK : Convex ℝ K)
    (r : K → ℂ) (hrange : ∀ x, r x ∈ K) (p : K × Set.Icc (0 : ℝ) 1) :
    straightLineDeformation r p ∈ K :=
  hK p.1.2 (hrange p.1) (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel _ _)

/-- The straight-line deformation stays in the convex domain. -/
noncomputable def retractionDeformation {K : Set ℂ} (hK : Convex ℝ K)
    (r : K → ℂ) (hrange : ∀ x, r x ∈ K) :
    K × Set.Icc (0 : ℝ) 1 → K :=
  fun p => ⟨straightLineDeformation r p, straightLineDeformation_mem hK r hrange p⟩

theorem continuous_retractionDeformation {K : Set ℂ} (hK : Convex ℝ K)
    (r : K → ℂ) (hrange : ∀ x, r x ∈ K) (hr : Continuous r) :
    Continuous (retractionDeformation hK r hrange) :=
  (continuous_straightLineDeformation hr).subtype_mk _

/-- Every supplied retraction of a convex domain onto the Mandelbrot set
extends to a strong deformation retraction. The homotopy is domain-valued,
starts at the identity, ends in the Mandelbrot set, and fixes it at all times. -/
theorem mandelbrot_strongDeformationRetract_of_retraction
    {K : Set ℂ} (hK : Convex ℝ K) (hMK : MLC.mandelbrotSet ⊆ K)
    (r : K → ℂ) (hr : Continuous r)
    (hrange : ∀ x, r x ∈ MLC.mandelbrotSet)
    (hfix : ∀ c (hc : c ∈ MLC.mandelbrotSet), r ⟨c, hMK hc⟩ = c) :
    ∃ H : K × Set.Icc (0 : ℝ) 1 → K, Continuous H ∧
      (∀ x, H (x, ⟨0, by norm_num⟩) = x) ∧
      (∀ x, (H (x, ⟨1, by norm_num⟩)).1 = r x) ∧
      (∀ c (hc : c ∈ MLC.mandelbrotSet) t,
        H (⟨c, hMK hc⟩, t) = ⟨c, hMK hc⟩) := by
  refine ⟨retractionDeformation hK r (fun x => hMK (hrange x)),
    continuous_retractionDeformation hK r _ hr, ?_, ?_, ?_⟩
  · intro x
    exact Subtype.ext (straightLineDeformation_zero r x)
  · intro x
    exact straightLineDeformation_one r x
  · intro c hc t
    exact Subtype.ext (straightLineDeformation_fixed ⟨c, hMK hc⟩ (hfix c hc) t)

end MLC.UniformGeometry
