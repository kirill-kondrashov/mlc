import Mlc.CategoricalTopologicalApproximation
import Mlc.ParaPuzzleConnectivity
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

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
* `SpaceHolomorphicCarvingData` is the genuine dynamical input: a connected
  source, a space-holomorphic map, and an exact image identification with the
  Green-sublevel/Mandelbrot intersection.

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

/-- The genuine dynamical bridge required to turn the abstract tower into
    the current parameter-frontier theorem. -/
structure SpaceHolomorphicCarvingData (c : ℂ) (n : ℕ) where
  hc : c ∈ MandelbrotSet
  map : ℂ → ℂ
  mapsTo :
    MapsTo map
      {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
  differentiableOn_map :
    DifferentiableOn ℂ map {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
  image_eq :
    map '' {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} =
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)

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
