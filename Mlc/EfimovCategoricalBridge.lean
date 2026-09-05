import Mlc.CategoricalTopologicalApproximation
import Mlc.ParaPuzzleConnectivity
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Efimov-style categorical bridge

This module records the part of an Efimov-style strategy that can be stated
honestly with the current Mathlib foundations.

Mathlib does not provide stable infinity-categories or algebraic `K`-theory.
Accordingly, the definitions below are interfaces, not implementations of
those theories:

* `DualizablePacmanTower` records a tower of rigid monoidal categories and
  adjoint refinement functors.
* `StrongMittagLefflerData` records the two categorical stabilization clauses
  used in Efimov's definition.
* `PacmanKTheory` records a graded additive-valued finite-level invariant.
* `PacmanRealization` records a compatible realization into the existing
  topological over-category.
* `SpaceHolomorphicCarvingData` is the genuine dynamical input for the current
  frozen model: a connected source, a space-holomorphic map, and an exact image
  identification with the full Green-sublevel/Mandelbrot intersection.
* `FiniteEtaleKZeroProbe` is the finite-etale/component-level shadow of a
  degree-zero localizing invariant; its triviality is equivalent to
  connectedness for nonempty subsets of `ℂ`.
* `DouadyHubbardYoccozCategoricalCarvingData` and
  `DouadyHubbardYoccozCategoricalTheorem` express the parameter--dynamical
  carving for that frozen model as a surjective morphism in `TopCat` and prove
  its connected-image consequence.

No field in this file is an axiom of the root theorem. The final theorem is
only the standard connected-image implication from the carving datum.
-/

namespace MLC
namespace Efimov

open CategoryTheory CategoryTheory.Limits Set Topology
open Quadratic Complex
open MLC.Categorical

noncomputable section

abbrev TowerIndex := ℕᵒᵖ

/-- A categorical sequence is essentially constant when it is eventually
    isomorphic to one fixed value. -/
def EventuallyEssentiallyConstant {C D : Type*} [Category C] [Category D]
    (F : ℕ → (C ⥤ D)) : Prop :=
  ∃ N : ℕ, ∀ m, N ≤ m → Nonempty (F m ≅ F N)

/-- A rigid monoidal category level for the abstract Pacman tower. -/
structure DualizableCatLevel where
  carrier : Type
  category : Category carrier
  monoidal : @MonoidalCategory carrier category
  rigid : @RigidCategory carrier category monoidal

instance (C : DualizableCatLevel) : Category C.carrier :=
  C.category

instance (C : DualizableCatLevel) : MonoidalCategory C.carrier :=
  C.monoidal

instance (C : DualizableCatLevel) : RigidCategory C.carrier :=
  C.rigid

/-- A tower of dualizable categorical Pacman models with adjacent refinement
    functors and chosen right adjoints.

    The current repository has no category of stable infinity-categories, so
    this is the strongest native Mathlib-level replacement: every level is
    explicitly rigid monoidal and every refinement carries an adjunction. -/
structure DualizablePacmanTower where
  level : ℕ → DualizableCatLevel
  transition : ∀ n, (level (n + 1)).carrier ⥤ (level n).carrier
  rightAdjoint : ∀ n, (level n).carrier ⥤ (level (n + 1)).carrier
  transitionAdjunction : ∀ n, Adjunction (transition n) (rightAdjoint n)
  rightAdjointPreservesColimits :
    ∀ n, PreservesColimits (rightAdjoint n)

/-- The eventual-stabilization clause used for the endofunctors
    `Fₘₙ Fₘₙᴿ` in Efimov's strong Mittag--Leffler condition. -/
structure StrongMittagLefflerData (T : DualizablePacmanTower) where
  transitionFrom :
    ∀ n d, (T.level (n + d)).carrier ⥤ (T.level n).carrier
  rightAdjointFrom :
    ∀ n d, (T.level n).carrier ⥤ (T.level (n + d)).carrier
  transitionFrom_zero : ∀ n, transitionFrom n 0 ≅ 𝟭 (T.level n).carrier
  transitionFrom_succ :
    ∀ n d,
      transitionFrom n (d + 1) ≅
        T.transition (n + d) ⋙ transitionFrom n d
  rightAdjointFrom_zero : ∀ n, rightAdjointFrom n 0 ≅ 𝟭 (T.level n).carrier
  rightAdjointFrom_succ :
    ∀ n d,
      rightAdjointFrom n (d + 1) ≅
        rightAdjointFrom n d ⋙ T.rightAdjoint (n + d)
  /-- Efimov's condition (ML1): the inverse sequence of
      `Fₘₙ Fₘₙᴿ` is essentially constant. -/
  ml1 :
    ∀ n,
      EventuallyEssentiallyConstant
        (fun d => rightAdjointFrom n d ⋙ transitionFrom n d)
  /-- The functors `Φₙₖ` supplied by the pro-limit construction in Efimov's
      condition (ML2). -/
  phi :
    ∀ n k, (T.level n).carrier ⥤ (T.level k).carrier
  phiLeftAdjoint :
    ∀ n k, (T.level k).carrier ⥤ (T.level n).carrier
  phiRightAdjoint :
    ∀ n k, (T.level k).carrier ⥤ (T.level n).carrier
  phiLeftAdjunction : ∀ n k, Adjunction (phiLeftAdjoint n k) (phi n k)
  phiRightAdjunction : ∀ n k, Adjunction (phi n k) (phiRightAdjoint n k)
  phiRightAdjointPreservesColimits :
    ∀ n k, PreservesColimits (phiRightAdjoint n k)

/-- The graded additive target used as a native stand-in for finite-level
    `K_n`-groups. The actual algebraic `K`-theory functor is intentionally not
    asserted because it is not present in Mathlib. -/
abbrev KTheoryTarget :=
  GradedObject ℤ AddCommGrpCat

/-- A finite-level graded invariant together with transition-compatible
    levelwise functors. -/
structure PacmanKTheory (T : DualizablePacmanTower) where
  values : TowerIndex ⥤ KTheoryTarget
  levelInvariant :
    ∀ n, (T.level n).carrier ⥤ KTheoryTarget
  transitionCompatibility :
    ∀ n,
      levelInvariant (n + 1) ≅
        T.transition n ⋙ levelInvariant n

/-- The degree-`d` type-valued shadow of a graded $K$-theory diagram. -/
def kComponent (K : PacmanKTheory T) (d : ℤ) : TowerIndex ⥤ Type :=
  K.values ⋙ GradedObject.eval d ⋙ forget AddCommGrpCat

/-- The native Mathlib Mittag--Leffler condition checked degree-by-degree on
    the graded finite-level invariant. This is a concrete necessary shadow of
    the stronger categorical condition above. -/
def KTheoryMittagLeffler (K : PacmanKTheory T) : Prop :=
  ∀ d : ℤ, (kComponent K d).IsMittagLeffler

theorem eventuallyEssentiallyConstant_const
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :
    EventuallyEssentiallyConstant (fun _ : ℕ => F) := by
  refine ⟨0, ?_⟩
  intro m hm
  exact ⟨Iso.refl F⟩

theorem constant_type_diagram_isMittagLeffler (A : Type*) :
    ((Functor.const TowerIndex).obj A).IsMittagLeffler := by
  apply Functor.isMittagLeffler_of_surjective
  intro i j f
  simpa using (Function.surjective_id : Function.Surjective (id : A → A))

theorem kTheory_eventualRange_attained
    (K : PacmanKTheory T) (hK : KTheoryMittagLeffler K) (d : ℤ) (j : TowerIndex) :
    ∃ (i : TowerIndex) (f : i ⟶ j),
      (kComponent K d).eventualRange j =
        Set.range ((kComponent K d).map f) :=
  ((kComponent K d).isMittagLeffler_iff_eventualRange.mp (hK d)) j

/-- An explicit comparison object for the continuous $K$-theory output of the
    tower. The isomorphism is the point at which Efimov's inverse-limit theorem
    would be instantiated; it is not inferred from the current Mathlib APIs. -/
structure KTheoryLimitComparison
    (K : PacmanKTheory T) [HasLimit K.values] where
  continuousLimit : KTheoryTarget
  comparison : continuousLimit ≅ limit K.values

/-- A realization family from every dualizable Pacman level to the existing
    topological approximation category over the parameter plane. -/
structure PacmanRealization (T : DualizablePacmanTower) where
  realize : ∀ n, (T.level n).carrier ⥤ Approximation
  transitionCompatibility :
    ∀ n,
      realize (n + 1) ≅ T.transition n ⋙ realize n

/-- The un-intersected parameter translate used by the
    Douady--Hubbard/Yoccoz carving statement. -/
def greenSublevelTranslateSet (c : ℂ) (n : ℕ) : Set ℂ :=
  {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}

/-- The Green-sublevel/Mandelbrot pullback as a parameter set. -/
def greenSublevelIntersectionSet (c : ℂ) (n : ℕ) : Set ℂ :=
  greenSublevelTranslateSet c n ∩ MandelbrotSet

/-- The genuine dynamical bridge required to turn the abstract tower into
    the current parameter-frontier theorem. -/
structure SpaceHolomorphicCarvingData (c : ℂ) (n : ℕ) where
  hc : c ∈ MandelbrotSet
  map : ℂ → ℂ
  mapsTo :
    MapsTo map
      (greenSublevelTranslateSet c n)
      (greenSublevelIntersectionSet c n)
  differentiableOn_map :
    DifferentiableOn ℂ map (greenSublevelTranslateSet c n)
  image_eq :
    map '' (greenSublevelTranslateSet c n) =
      greenSublevelIntersectionSet c n

/-- A surjective morphism in `TopCat` between subspaces of the parameter
    plane. In the topological category, this is the concrete
    regular-epimorphic part of a carving map that is needed for connectedness
    transport. -/
structure TopCatSurjectiveMorphism (S T : Set ℂ) where
  hom : TopCat.of S ⟶ TopCat.of T
  surjective : Function.Surjective hom.hom

theorem isConnected_of_topCatSurjectiveMorphism
    {S T : Set ℂ} (hS : IsConnected S)
    (h : TopCatSurjectiveMorphism S T) :
    IsConnected T := by
  letI : ConnectedSpace S := Subtype.connectedSpace hS
  have hT : ConnectedSpace T := by
    rw [connectedSpace_iff_univ]
    have hcontinuous : Continuous h.hom.hom :=
      ContinuousMap.continuous_toFun h.hom.hom
    have himage : IsConnected (Set.range h.hom.hom) := by
      simpa only [Set.image_univ] using
        (isConnected_univ.image h.hom.hom hcontinuous.continuousOn)
    rw [h.surjective.range_eq] at himage
    exact himage
  exact isConnected_iff_connectedSpace.mpr hT

/-- The categorical form of the Douady--Hubbard/Yoccoz carving datum:
    a connected Green-sublevel source admits a surjective `TopCat` morphism
    onto the Green-sublevel/Mandelbrot pullback. -/
structure DouadyHubbardYoccozCategoricalCarvingData (c : ℂ) (n : ℕ) where
  hc : c ∈ MandelbrotSet
  carving :
    TopCatSurjectiveMorphism
      (greenSublevelTranslateSet c n)
      (greenSublevelIntersectionSet c n)

theorem isConnected_greenSublevelIntersection_of_douadyHubbardYoccozCarving
    {c : ℂ} {n : ℕ}
    (h : DouadyHubbardYoccozCategoricalCarvingData c n) :
    IsConnected (greenSublevelIntersectionSet c n) :=
  isConnected_of_topCatSurjectiveMorphism
    (by simpa [greenSublevelTranslateSet] using
      green_sublevel_translate_connected h.hc n)
    h.carving

def SpaceHolomorphicCarvingData.toDouadyHubbardYoccozCategoricalCarvingData
    {c : ℂ} {n : ℕ} (h : SpaceHolomorphicCarvingData c n) :
    DouadyHubbardYoccozCategoricalCarvingData c n := by
  refine
    { hc := h.hc
      carving :=
        { hom := TopCat.ofHom
            { toFun := fun z : greenSublevelTranslateSet c n =>
                ⟨h.map (z : ℂ), h.mapsTo z.property⟩
              continuous_toFun := by
                apply Continuous.subtype_mk
                exact continuousOn_iff_continuous_restrict.mp
                  h.differentiableOn_map.continuousOn }
          surjective := ?_ } }
  intro y
  have hy : (y : ℂ) ∈ h.map '' greenSublevelTranslateSet c n := by
    rw [h.image_eq]
    exact y.property
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext hxy

/-- The categorical Douady--Hubbard/Yoccoz parameter--dynamical theorem,
    restricted to the straddling pieces. -/
def DouadyHubbardYoccozCategoricalTheorem : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ greenSublevelTranslateSet c n ⊆ MandelbrotSet →
      Nonempty (DouadyHubbardYoccozCategoricalCarvingData c n)

theorem greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz
    (h : DouadyHubbardYoccozCategoricalTheorem) :
    GreenSublevelIntersectionCategoricalData := by
  intro c hc n hfactor
  have hstraddle : ¬ greenSublevelTranslateSet c n ⊆ MandelbrotSet := by
    intro hsub
    apply hfactor
    apply factorsThrough_ofSet_iff.mpr
    simpa [greenSublevelTranslateSet, greenSublevelApproximation,
      mandelbrotApproximation] using hsub
  obtain ⟨hcarving⟩ := h c hc n hstraddle
  have hconnected :=
    isConnected_greenSublevelIntersection_of_douadyHubbardYoccozCarving hcarving
  change IsConnected
    (image (intersection (greenSublevelApproximation c n) mandelbrotApproximation))
  rw [image_intersection]
  simpa [greenSublevelTranslateSet, greenSublevelIntersectionSet,
    greenSublevelApproximation, mandelbrotApproximation, image_ofSet] using
    hconnected

theorem douadyHubbardYoccozCategoricalTheorem_of_spaceHolomorphicCarving
    (h :
      ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
        ¬ greenSublevelTranslateSet c n ⊆ MandelbrotSet →
          Nonempty (SpaceHolomorphicCarvingData c n)) :
    DouadyHubbardYoccozCategoricalTheorem := by
  intro c hc n hstraddle
  obtain ⟨hcarving⟩ := h c hc n hstraddle
  exact ⟨hcarving.toDouadyHubbardYoccozCategoricalCarvingData⟩

theorem greenSublevelIntersectionCategoricalData_of_spaceHolomorphicCarving
    (h :
      ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
        ¬ greenSublevelTranslateSet c n ⊆ MandelbrotSet →
          Nonempty (SpaceHolomorphicCarvingData c n)) :
    GreenSublevelIntersectionCategoricalData :=
  greenSublevelIntersectionCategoricalData_of_douadyHubbardYoccoz
    (douadyHubbardYoccozCategoricalTheorem_of_spaceHolomorphicCarving h)

/-- The finite-etale, degree-zero component probe of a space.

    Efimov's continuous `K`-theory is not available in Mathlib, so this is
    deliberately only its component-level shadow: locally constant
    two-valued functions detect clopen decompositions. -/
abbrev FiniteEtaleKZeroProbe (S : Set ℂ) :=
  LocallyConstant S Bool

/-- The component probe is trivial when every finite-etale two-point object is
    pulled back from one point. -/
def FiniteEtaleKZeroProbeTrivial (S : Set ℂ) : Prop :=
  ∀ f : FiniteEtaleKZeroProbe S, ∃ b : Bool, f = LocallyConstant.const S b

theorem finiteEtaleKZeroProbeTrivial_of_isConnected {S : Set ℂ}
    (hS : IsConnected S) : FiniteEtaleKZeroProbeTrivial S := by
  obtain ⟨x, hx⟩ := hS.nonempty
  letI : PreconnectedSpace S := Subtype.preconnectedSpace hS.isPreconnected
  intro f
  refine ⟨f ⟨x, hx⟩, ?_⟩
  ext y
  exact f.apply_eq_of_preconnectedSpace y ⟨x, hx⟩

theorem isConnected_of_finiteEtaleKZeroProbeTrivial {S : Set ℂ}
    (hS : S.Nonempty) (hprobe : FiniteEtaleKZeroProbeTrivial S) :
    IsConnected S := by
  refine ⟨hS, ?_⟩
  apply isPreconnected_of_forall_constant
  intro f hf x hx y hy
  let g : FiniteEtaleKZeroProbe S :=
    { toFun := fun z : S => f z
      isLocallyConstant :=
        (IsLocallyConstant.iff_continuous _).2
          (continuousOn_iff_continuous_restrict.mp hf) }
  obtain ⟨b, hgb⟩ := hprobe g
  have hxg := congrArg (fun q => q ⟨x, hx⟩) hgb
  have hyg := congrArg (fun q => q ⟨y, hy⟩) hgb
  exact (show f x = b from hxg) |>.trans (show b = f y from hyg.symm)

theorem isConnected_iff_finiteEtaleKZeroProbeTrivial {S : Set ℂ}
    (hS : S.Nonempty) :
    IsConnected S ↔ FiniteEtaleKZeroProbeTrivial S := by
  constructor
  · exact finiteEtaleKZeroProbeTrivial_of_isConnected
  · exact isConnected_of_finiteEtaleKZeroProbeTrivial hS

/-- A finite-stage descent certificate for the component probe.

    This is the concrete topological obligation suggested by Efimov's
    strongly Mittag--Leffler inverse-limit formalism. It asks that every
    finite-etale probe on `S` descend along one stage projection, while each
    stage is connected. It is weaker than constructing a space-holomorphic
    carving map and is independent of the unavailable stable
    infinity-categorical machinery. -/
structure FiniteEtaleKZeroDescentData (S : Set ℂ) where
  stage : ℕ → Set ℂ
  projection : ∀ k, ContinuousMap S (stage k)
  stageConnected : ∀ k, IsConnected (stage k)
  descend :
    ∀ f : FiniteEtaleKZeroProbe S, ∃ k : ℕ, ∃ g : FiniteEtaleKZeroProbe (stage k),
      f = LocallyConstant.comap (projection k) g

theorem isConnected_of_finiteEtaleKZeroDescent
    {S : Set ℂ} (hS : S.Nonempty)
    (hdesc : FiniteEtaleKZeroDescentData S) :
    IsConnected S := by
  apply isConnected_of_finiteEtaleKZeroProbeTrivial hS
  intro f
  obtain ⟨k, g, hfg⟩ := hdesc.descend f
  obtain ⟨b, hgb⟩ :=
    finiteEtaleKZeroProbeTrivial_of_isConnected (hdesc.stageConnected k) g
  refine ⟨b, ?_⟩
  rw [hfg, hgb]
  rfl

/-- The inclusion of one parameter subset into another, used to restrict
    finite-etale probes. -/
def finiteEtaleKZeroInclusion {S T : Set ℂ} (hST : S ⊆ T) :
    ContinuousMap S T where
  toFun := fun z => ⟨(z : ℂ), hST z.property⟩
  continuous_toFun :=
    Continuous.subtype_mk continuous_subtype_val (fun z => hST z.property)

/-- Restriction of a finite-etale component probe along a subset inclusion. -/
def finiteEtaleKZeroRestriction {S T : Set ℂ} (hST : S ⊆ T) :
    FiniteEtaleKZeroProbe T → FiniteEtaleKZeroProbe S :=
  fun f => LocallyConstant.comap (finiteEtaleKZeroInclusion hST) f

def FiniteEtaleKZeroRestrictionSurjective {S T : Set ℂ} (hST : S ⊆ T) : Prop :=
  Function.Surjective (finiteEtaleKZeroRestriction hST)

theorem finiteEtaleKZeroRestrictionSurjective_of_isConnected
    {S T : Set ℂ} (hST : S ⊆ T) (hS : IsConnected S) :
    FiniteEtaleKZeroRestrictionSurjective hST := by
  intro f
  obtain ⟨b, hfb⟩ := finiteEtaleKZeroProbeTrivial_of_isConnected hS f
  refine ⟨LocallyConstant.const T b, ?_⟩
  rw [hfb]
  rfl

/-! ### Relative `K₀` excision criterion -/

theorem isConnected_of_finiteEtaleKZeroRestrictionSurjective
    {S T : Set ℂ} (hST : S ⊆ T) (hS : S.Nonempty) (hT : IsConnected T)
    (hrestriction : FiniteEtaleKZeroRestrictionSurjective (S := S) (T := T) hST) :
    IsConnected S := by
  apply isConnected_of_finiteEtaleKZeroProbeTrivial hS
  intro f
  obtain ⟨g, hgf⟩ := hrestriction f
  obtain ⟨b, hgb⟩ := finiteEtaleKZeroProbeTrivial_of_isConnected hT g
  refine ⟨b, ?_⟩
  rw [← hgf, hgb]
  rfl

theorem finiteEtaleKZeroRestrictionSurjective_iff_isConnected
    {S T : Set ℂ} (hST : S ⊆ T) (hS : S.Nonempty) (hT : IsConnected T) :
    FiniteEtaleKZeroRestrictionSurjective hST ↔ IsConnected S := by
  constructor
  · exact isConnected_of_finiteEtaleKZeroRestrictionSurjective hST hS hT
  · exact finiteEtaleKZeroRestrictionSurjective_of_isConnected hST

/-! ### Categorical pullback criterion -/

/-- Triviality of the finite-etale component probe of a categorical
    approximation. -/
def FiniteEtaleKZeroProbeTrivialApproximation (A : Approximation) : Prop :=
  FiniteEtaleKZeroProbeTrivial (image A)

theorem imageConnected_iff_finiteEtaleKZeroProbeTrivialApproximation
    {A : Approximation} (hA : (image A).Nonempty) :
    ImageConnected A ↔ FiniteEtaleKZeroProbeTrivialApproximation A := by
  change IsConnected (image A) ↔ FiniteEtaleKZeroProbeTrivial (image A)
  exact isConnected_iff_finiteEtaleKZeroProbeTrivial hA

theorem image_intersection_subset_left (A B : Approximation) :
    image (intersection A B) ⊆ image A := by
  rw [image_intersection]
  exact inter_subset_left

/-- Relative finite-etale `K₀` excision for a pullback in `TopCat / ℂ`.

    This is the component-level shadow of the vanishing of a relative
    localizing invariant: every finite-etale probe on the pullback extends
    along the left leg of the pullback. -/
def FiniteEtaleKZeroPullbackExcision (A B : Approximation) : Prop :=
  FiniteEtaleKZeroRestrictionSurjective
    (image_intersection_subset_left A B)

theorem imageConnected_intersection_of_finiteEtaleKZeroPullbackExcision
    {A B : Approximation} (hnonempty : (image (intersection A B)).Nonempty)
    (hA : ImageConnected A)
    (hExc : FiniteEtaleKZeroPullbackExcision A B) :
    ImageConnected (intersection A B) := by
  change IsConnected (image (intersection A B))
  exact isConnected_of_finiteEtaleKZeroRestrictionSurjective
    (image_intersection_subset_left A B) hnonempty hA hExc

/-- The target-specific pullback form of the finite-etale `K₀` input. -/
def GreenSublevelIntersectionFiniteEtaleKZeroPullbackData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
      FiniteEtaleKZeroPullbackExcision
        (greenSublevelApproximation c n) mandelbrotApproximation

theorem greenSublevelIntersectionSet_nonempty {c : ℂ}
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    (greenSublevelIntersectionSet c n).Nonempty := by
  refine ⟨c, ?_, hc⟩
  change green_function c (c - c) < (1 / 2 : ℝ) ^ n
  have h0 := Quadratic.green_sublevel_contains_0 c n hc
  change green_function c 0 < (1 / 2 : ℝ) ^ n at h0
  simpa [sub_self] using h0

theorem greenSublevelIntersectionCategoricalData_of_finiteEtaleKZeroPullbackData
    (h : GreenSublevelIntersectionFiniteEtaleKZeroPullbackData) :
    GreenSublevelIntersectionCategoricalData := by
  intro c hc n hstraddle
  apply imageConnected_intersection_of_finiteEtaleKZeroPullbackExcision
  · rw [image_intersection]
    simpa [greenSublevelIntersectionSet, greenSublevelTranslateSet,
      greenSublevelApproximation,
      mandelbrotApproximation, image_ofSet] using
      (greenSublevelIntersectionSet_nonempty hc n)
  · change IsConnected (image (greenSublevelApproximation c n))
    simpa [greenSublevelApproximation, image_ofSet] using
      (green_sublevel_translate_connected hc n)
  · exact h c hc n hstraddle

theorem greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroPullbackData :
    GreenSublevelIntersectionCategoricalData ↔
      GreenSublevelIntersectionFiniteEtaleKZeroPullbackData := by
  constructor
  · intro h c hc n hstraddle
    have hset :
        ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) := by
      intro hsub
      apply hstraddle
      apply factorsThrough_ofSet_iff.mpr
      simpa [greenSublevelApproximation, mandelbrotApproximation] using hsub
    have hconn :=
      (greenSublevelIntersectionCategoricalData_iff.mp h) c hc n hset
    change FiniteEtaleKZeroRestrictionSurjective
      (image_intersection_subset_left
        (greenSublevelApproximation c n) mandelbrotApproximation)
    apply finiteEtaleKZeroRestrictionSurjective_of_isConnected
      (image_intersection_subset_left
        (greenSublevelApproximation c n) mandelbrotApproximation)
    simpa [image_intersection, greenSublevelApproximation,
      mandelbrotApproximation, image_ofSet] using hconn
  · exact greenSublevelIntersectionCategoricalData_of_finiteEtaleKZeroPullbackData

def GreenSublevelIntersectionFiniteEtaleKZeroData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) →
      FiniteEtaleKZeroProbeTrivial (greenSublevelIntersectionSet c n)

theorem greenSublevelIntersectionSetData_iff_finiteEtaleKZeroData :
    GreenSublevelIntersectionSetData ↔
      GreenSublevelIntersectionFiniteEtaleKZeroData := by
  constructor
  · intro h c hc n hstraddle
    exact (isConnected_iff_finiteEtaleKZeroProbeTrivial
      (greenSublevelIntersectionSet_nonempty hc n)).mp (by
        simpa [greenSublevelIntersectionSet, greenSublevelTranslateSet] using
          h c hc n hstraddle)
  · intro h c hc n hstraddle
    have hstraddle' :
        ¬ greenSublevelTranslateSet c n ⊆ MandelbrotSet := by
      simpa [greenSublevelTranslateSet] using hstraddle
    exact (isConnected_iff_finiteEtaleKZeroProbeTrivial
      (greenSublevelIntersectionSet_nonempty hc n)).mpr
      (h c hc n hstraddle')

theorem greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroData :
    GreenSublevelIntersectionCategoricalData ↔
      GreenSublevelIntersectionFiniteEtaleKZeroData :=
  greenSublevelIntersectionCategoricalData_iff.trans
    greenSublevelIntersectionSetData_iff_finiteEtaleKZeroData

theorem greenSublevelIntersectionSet_subset_greenSublevel (c : ℂ) (n : ℕ) :
    greenSublevelIntersectionSet c n ⊆
      {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} :=
  fun _ hz => hz.1

/-! A localizing-invariant interpretation: vanishing of the relative
    component-level term is represented here by surjectivity of restriction
    on finite-etale probes. -/

def GreenSublevelIntersectionFiniteEtaleKZeroExcisionData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) →
      FiniteEtaleKZeroRestrictionSurjective
        (greenSublevelIntersectionSet_subset_greenSublevel c n)

theorem greenSublevelIntersectionSetData_iff_finiteEtaleKZeroExcisionData :
    GreenSublevelIntersectionSetData ↔
      GreenSublevelIntersectionFiniteEtaleKZeroExcisionData := by
  constructor
  · intro h c hc n hstraddle
    exact finiteEtaleKZeroRestrictionSurjective_of_isConnected
      (greenSublevelIntersectionSet_subset_greenSublevel c n)
      (h c hc n hstraddle)
  · intro h c hc n hstraddle
    exact isConnected_of_finiteEtaleKZeroRestrictionSurjective
      (greenSublevelIntersectionSet_subset_greenSublevel c n)
      (greenSublevelIntersectionSet_nonempty hc n)
      (green_sublevel_translate_connected hc n)
      (h c hc n hstraddle)

theorem greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroExcisionData :
    GreenSublevelIntersectionCategoricalData ↔
      GreenSublevelIntersectionFiniteEtaleKZeroExcisionData :=
  greenSublevelIntersectionCategoricalData_iff.trans
    greenSublevelIntersectionSetData_iff_finiteEtaleKZeroExcisionData

theorem greenSublevelIntersectionCategoricalData_of_finiteEtaleKZeroExcision
    (h : GreenSublevelIntersectionFiniteEtaleKZeroExcisionData) :
    GreenSublevelIntersectionCategoricalData :=
  greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroExcisionData.mpr h

/-- A target-specific Efimov bridge can replace exact image carving by
    relative finite-etale `K₀` excision on the categorical pullback. -/
structure EfimovGreenSublevelKZeroBridge
    (T : DualizablePacmanTower) (K : PacmanKTheory T) [HasLimit K.values] where
  strongMittagLeffler : StrongMittagLefflerData T
  kTheoryMittagLeffler : KTheoryMittagLeffler K
  kTheoryLimit : KTheoryLimitComparison K
  realization : PacmanRealization T
  pullbackExcision :
    GreenSublevelIntersectionFiniteEtaleKZeroPullbackData

theorem greenSublevelIntersectionCategorical_of_efimovKZeroBridge
    {T : DualizablePacmanTower} {K : PacmanKTheory T} {c : ℂ} {n : ℕ}
    [HasLimit K.values] (h : EfimovGreenSublevelKZeroBridge T K)
    (hc : c ∈ MandelbrotSet)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet)) :
    ImageConnected
      (intersection (greenSublevelApproximation c n) mandelbrotApproximation) := by
  have hcatData : GreenSublevelIntersectionCategoricalData :=
    greenSublevelIntersectionCategoricalData_iff_finiteEtaleKZeroPullbackData.mpr
      h.pullbackExcision
  apply hcatData c hc n
  intro hfactor
  apply hstraddle
  simpa [greenSublevelApproximation, mandelbrotApproximation] using
    (factorsThrough_ofSet_iff.mp hfactor)

/-- A complete conditional bridge assembling Efimov-style categorical data
    with the parameter realization/carving datum. -/
structure EfimovRealizationCarvingBridge
    (T : DualizablePacmanTower) (K : PacmanKTheory T) (c : ℂ) (n : ℕ)
    [HasLimit K.values] where
  strongMittagLeffler : StrongMittagLefflerData T
  kTheoryMittagLeffler : KTheoryMittagLeffler K
  kTheoryLimit : KTheoryLimitComparison K
  realization : PacmanRealization T
  carving : SpaceHolomorphicCarvingData c n

theorem isConnected_greenSublevel_inter_mandelbrot_of_spaceHolomorphicCarving
    {c : ℂ} {n : ℕ} (h : SpaceHolomorphicCarvingData c n) :
    IsConnected
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  change IsConnected (greenSublevelIntersectionSet c n)
  rw [← h.image_eq]
  exact
    (green_sublevel_translate_connected h.hc n).image h.map
      h.differentiableOn_map.continuousOn

theorem greenSublevelIntersectionCategorical_of_efimovBridge
    {T : DualizablePacmanTower} {K : PacmanKTheory T} {c : ℂ} {n : ℕ}
    [HasLimit K.values] (h : EfimovRealizationCarvingBridge T K c n) :
    ImageConnected
      (intersection (greenSublevelApproximation c n) mandelbrotApproximation) := by
  have h_connected :=
    isConnected_greenSublevel_inter_mandelbrot_of_spaceHolomorphicCarving h.carving
  change IsConnected
    (image (intersection (greenSublevelApproximation c n) mandelbrotApproximation))
  rw [image_intersection]
  simpa [greenSublevelApproximation, mandelbrotApproximation, image_ofSet] using h_connected

end
end Efimov
end MLC
