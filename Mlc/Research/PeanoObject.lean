import Mlc.Research.Dimension
import Mlc.CategoricalRoot
import Mathlib.Topology.Category.CompHaus.EffectiveEpi
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Peano objects: the local connectivity of a continuum as a morphism from the interval

The Hahn–Mazurkiewicz theorem says that a continuum (compact, connected, metrizable) is locally
connected exactly when it is a continuous image of the interval, and Carathéodory's theorem says
that for a full continuum this holds exactly when the Riemann map of its complement extends
continuously to the circle. For the Mandelbrot set, if MLC holds, the boundary values of the
exterior Riemann map, the landing map of the external rays, parametrize the boundary. This module
states the first form in the category of compact Hausdorff spaces, next to the categorical root
`Mlc/CategoricalRoot.lean`, and brings in the dimension of `Mlc/Research/Dimension.lean`.

* **Definition `IsPeanoObject X`**: the object `X` of `CompHaus` is an epimorphic image of the
  interval (`intervalObject`). In `CompHaus` the epimorphisms are the surjections.
* **Theorem `IsPeanoObject.locallyConnectedSpace`**: a Peano object is locally connected, because a
  surjection of a compact space onto a Hausdorff space is a quotient map, and a quotient of a
  locally connected space is locally connected (`locallyConnectedSpace_of_isQuotientMap`).
* **Theorem `IsPeanoObject.exists_regularEpi`** (the quotient form): in `CompHaus` the
  epimorphisms are the effective ones, so the parametrization of a Peano object is a regular
  epimorphism, the coequalizer of its kernel pair: the object is the quotient of the interval by a
  closed equivalence relation. For the Mandelbrot set this is some closed equivalence relation on
  the interval, the kernel pair of the chosen parametrization. The landing relation of the external
  rays lives on the circle of angles and gives the pinched-disk model of Thurston and
  Douady–Hubbard, a different statement that is not formalized.
* **Theorems `mlc_iff_peano` and `mlc_iff_regularEpi`**: given the Hahn–Mazurkiewicz theorem
  (`HahnMazurkiewicz`, published, not formalized, the converse for metrizable continua) and the
  connectedness of the Mandelbrot set (Douady–Hubbard), the categorical statement
  `Categorical.MLCConjecture` holds exactly when the Mandelbrot object `mandelbrotCompHaus` is a
  Peano object, exactly when it is a regular quotient of the interval. `categorical_mlc_of_peano`
  is the direction that needs no input.
* **Theorem `ShishikuraDimension.holder_exponent_le_half_of_epi`**: given Shishikura's theorem (the
  boundary of the Mandelbrot set has Hausdorff dimension `2`), no epimorphism from the interval onto
  the boundary object `boundaryCompHaus` is `α`-Hölder with `α > 1/2`, in particular none is
  Lipschitz. The fractal holds more dimension than the interval carries by a smooth map: the
  parametrization of the boundary that MLC provides is wild, and any Hölder control of the landing
  map has an exponent at most `1/2`.
-/

namespace MLC.Research

open CategoryTheory MeasureTheory ENNReal Set Topology Metric NNReal

noncomputable section

/-! ### Local connectivity passes to quotients -/

/-- A quotient of a locally connected space is locally connected: a connected component of an open
set of the quotient has an open preimage, because the image of a connected neighbourhood stays in
the component. -/
theorem locallyConnectedSpace_of_isQuotientMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyConnectedSpace X] {f : X → Y} (hf : Topology.IsQuotientMap f) :
    LocallyConnectedSpace Y := by
  refine locallyConnectedSpace_iff_connectedComponentIn_open.2 fun F hF y hy => ?_
  rw [← hf.isOpen_preimage, isOpen_iff_mem_nhds]
  intro x hx
  have hxF : f x ∈ F := connectedComponentIn_subset F y hx
  have hxo : IsOpen (connectedComponentIn (f ⁻¹' F) x) :=
    (hF.preimage hf.continuous).connectedComponentIn
  refine Filter.mem_of_superset (hxo.mem_nhds (mem_connectedComponentIn (hxF))) ?_
  intro x' hx'
  have himg : f '' connectedComponentIn (f ⁻¹' F) x ⊆ connectedComponentIn F (f x) :=
    (isPreconnected_connectedComponentIn.image f
      hf.continuous.continuousOn).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxF, rfl⟩
      ((image_mono (connectedComponentIn_subset _ _)).trans (image_preimage_subset f F))
  rw [connectedComponentIn_eq hx]
  exact himg ⟨x', hx', rfl⟩

/-! ### The interval, as an object of `CompHaus` -/

/-- The closed unit interval is locally connected (it is a manifold with boundary). -/
instance : LocallyConnectedSpace unitInterval := by
  haveI : LocPathConnectedSpace unitInterval :=
    ChartedSpace.locPathConnectedSpace (EuclideanHalfSpace 1) unitInterval
  infer_instance

/-- The closed unit interval as an object of the category of compact Hausdorff spaces. -/
abbrev intervalObject : CompHaus := CompHaus.of unitInterval

/-- **A Peano object.** An object of `CompHaus` is a Peano object if it is an epimorphic image of the
interval, that is, a continuous image of `[0, 1]`: a curve in the sense of Peano. -/
def IsPeanoObject (X : CompHaus) : Prop :=
  ∃ f : intervalObject ⟶ X, Epi f

/-- **A Peano object is locally connected.** An epimorphism of `CompHaus` is a surjection, a
surjection of a compact space onto a Hausdorff space is a quotient map, and a quotient of the
locally connected interval is locally connected. -/
theorem IsPeanoObject.locallyConnectedSpace {X : CompHaus} (h : IsPeanoObject X) :
    LocallyConnectedSpace X := by
  obtain ⟨f, hf⟩ := h
  have hsurj : Function.Surjective f := (CompHaus.epi_iff_surjective f).1 hf
  have hcont : Continuous f := f.hom.hom.continuous
  exact locallyConnectedSpace_of_isQuotientMap (hcont.isClosedMap.isQuotientMap hcont hsurj)

/-- **The Hahn–Mazurkiewicz theorem.** Every locally connected metrizable continuum is an epimorphic
image of the interval in `CompHaus`. Published; not formalized. -/
def HahnMazurkiewicz : Prop :=
  ∀ (X : CompHaus.{0}) [ConnectedSpace X] [TopologicalSpace.MetrizableSpace X],
    LocallyConnectedSpace X → IsPeanoObject X

/-- **The quotient form.** In `CompHaus` the epimorphisms are the effective ones, so the
parametrization of a Peano object is a regular epimorphism: the object is the coequalizer of the
kernel pair of the parametrization, the quotient of the interval by a closed equivalence relation.
For the Mandelbrot set this is some closed equivalence relation on the interval; the landing
relation of the external rays lives on the circle of angles and belongs to the pinched-disk model of
Thurston and Douady–Hubbard, which is not formalized. -/
theorem IsPeanoObject.exists_regularEpi {X : CompHaus.{0}} (h : IsPeanoObject X) :
    ∃ f : intervalObject ⟶ X, Nonempty (RegularEpi f) := by
  obtain ⟨f, hf⟩ := h
  haveI : EffectiveEpi f := ((CompHaus.effectiveEpi_tfae f).out 0 1).2 hf
  exact ⟨f, ⟨regularEpiOfEffectiveEpi f⟩⟩

/-! ### The Mandelbrot set and its boundary -/

instance : CompactSpace MLC.mandelbrotSet :=
  isCompact_iff_compactSpace.1 MLC.Quadratic.isCompact_mandelbrot

/-- The Mandelbrot set as an object of `CompHaus`. -/
abbrev mandelbrotCompHaus : CompHaus := CompHaus.of MLC.mandelbrotSet

/-- **MLC from a Peano parametrization.** If the Mandelbrot set is an epimorphic image of the
interval in `CompHaus`, the categorical statement `MLCConjecture` of `CategoricalRoot.lean` holds. -/
theorem categorical_mlc_of_peano (h : IsPeanoObject mandelbrotCompHaus) :
    Categorical.MLCConjecture :=
  h.locallyConnectedSpace

/-- **The categorical form of the Carathéodory–Hahn–Mazurkiewicz characterization of MLC.** Given
the connectedness of the Mandelbrot set (Douady–Hubbard) and the Hahn–Mazurkiewicz theorem, MLC
holds exactly when the Mandelbrot object is an epimorphic image of the interval. -/
theorem mlc_iff_peano (hHM : HahnMazurkiewicz) [ConnectedSpace MLC.mandelbrotSet] :
    Categorical.MLCConjecture ↔ IsPeanoObject mandelbrotCompHaus :=
  ⟨fun h => hHM mandelbrotCompHaus h, categorical_mlc_of_peano⟩

/-- **MLC as a quotient of the interval.** Given the connectedness of the Mandelbrot set and the
Hahn–Mazurkiewicz theorem, MLC holds exactly when the Mandelbrot object is a regular quotient of
the interval in `CompHaus`: the coequalizer of a closed equivalence relation on `[0, 1]`. This is
the categorical form of the Hahn–Mazurkiewicz parametrization; the pinched-disk model of the
external rays, a quotient of the closed disk by a lamination, is a different statement. -/
theorem mlc_iff_regularEpi (hHM : HahnMazurkiewicz) [ConnectedSpace MLC.mandelbrotSet] :
    Categorical.MLCConjecture ↔
      ∃ f : intervalObject ⟶ mandelbrotCompHaus, Nonempty (RegularEpi f) := by
  rw [mlc_iff_peano hHM]
  refine ⟨IsPeanoObject.exists_regularEpi, ?_⟩
  rintro ⟨f, ⟨hf⟩⟩
  haveI : IsRegularEpi f := ⟨⟨hf⟩⟩
  exact ⟨f, inferInstance⟩

instance : CompactSpace (frontier MLC.mandelbrotSet) :=
  isCompact_iff_compactSpace.1
    (MLC.Quadratic.isCompact_mandelbrot.of_isClosed_subset isClosed_frontier
      (MLC.Quadratic.isClosed_mandelbrot.frontier_subset))

/-- The boundary of the Mandelbrot set as an object of `CompHaus`. -/
abbrev boundaryCompHaus : CompHaus := CompHaus.of (frontier MLC.mandelbrotSet)

/-- The unit interval has Hausdorff dimension `1`. -/
lemma dimH_univ_unitInterval : dimH (Set.univ : Set unitInterval) = 1 := by
  rw [← isometry_subtype_coe.dimH_image, image_univ, Subtype.range_coe]
  rw [Real.dimH_of_nonempty_interior (by rw [interior_Icc]; exact nonempty_Ioo.2 zero_lt_one)]
  simp

/-- **No epimorphism from the interval onto the boundary of `M` is better than `1/2`-Hölder.**
Given Shishikura's theorem, an `α`-Hölder parametrization of the boundary of the Mandelbrot set by
the interval, an epimorphism of `CompHaus` read as a map into the plane, has `α ≤ 1/2`. The fractal
boundary holds more dimension than the interval can carry by a Lipschitz map. -/
theorem ShishikuraDimension.holder_exponent_le_half_of_epi (hS : ShishikuraDimension)
    (f : intervalObject ⟶ boundaryCompHaus) [Epi f] {C α : ℝ≥0} (hα : 0 < α)
    (hf : HolderWith C α fun t : unitInterval => ((f t : frontier MLC.mandelbrotSet) : ℂ)) :
    α ≤ 1 / 2 := by
  have hsurj : Function.Surjective f := (CompHaus.epi_iff_surjective f).1 inferInstance
  have hrange : Set.range (fun t : unitInterval => ((f t : frontier MLC.mandelbrotSet) : ℂ)) =
      frontier MLC.mandelbrotSet := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hz
      obtain ⟨t, ht⟩ := hsurj ⟨z, hz⟩
      refine ⟨t, ?_⟩
      show (((ConcreteCategory.hom f) t : frontier MLC.mandelbrotSet) : ℂ) = z
      rw [ht]
  have h1 := hf.dimH_range_le hα
  rw [hrange, hS, dimH_univ_unitInterval] at h1
  have h2 : ((2 : ℝ≥0) : ℝ≥0∞) ≤ 1 / α := by simpa using h1
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hα.ne')) (Or.inl (by simp))] at h2
  have h3 : (2 : ℝ≥0) * α ≤ 1 := by exact_mod_cast h2
  rw [← NNReal.coe_le_coe] at h3 ⊢
  push_cast at h3 ⊢
  linarith

end

end MLC.Research
