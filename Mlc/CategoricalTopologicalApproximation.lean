import Mathlib.Analysis.Complex.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

namespace MLC
namespace Categorical

open CategoryTheory CategoryTheory.Limits Set Topology

noncomputable section

/-- The ambient parameter plane as an object of `TopCat`. -/
abbrev parameterPlane : TopCat :=
  TopCat.of ℂ

/-- Topological approximations over the ambient parameter plane. -/
abbrev Approximation :=
  Over parameterPlane

/-- The continuous inclusion of a subset of the parameter plane. -/
def setInclusion (S : Set ℂ) : TopCat.of S ⟶ parameterPlane :=
  TopCat.ofHom
    { toFun := fun z : S => (z : ℂ)
      continuous_toFun := continuous_subtype_val }

/-- A subset with its subspace topology, regarded as an approximation. -/
def ofSet (S : Set ℂ) : Approximation :=
  Over.mk (setInclusion S)

/-- The image of an approximation in the ambient parameter plane. -/
def image (A : Approximation) : Set ℂ :=
  Set.range (A.hom : A.left → ℂ)

/-- An approximation factors through another one in the over-category. -/
def factorsThrough (A B : Approximation) : Prop :=
  Nonempty (A ⟶ B)

/-- The categorical intersection of two approximations is their pullback. -/
def intersection (A B : Approximation) : Approximation :=
  Over.mk (pullback.fst A.hom B.hom ≫ A.hom)

/-- The pullback universal property underlying `intersection`. -/
def intersection_is_pullback (A B : Approximation) :
    IsLimit (pullback.cone A.hom B.hom) :=
  pullback.isLimit _ _

/-- The image of a categorical intersection is the intersection of images. -/
theorem image_intersection (A B : Approximation) :
    image (intersection A B) = image A ∩ image B := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ⟨pullback.fst A.hom B.hom p, rfl⟩
    · refine ⟨pullback.snd A.hom B.hom p, ?_⟩
      change B.hom (pullback.snd A.hom B.hom p) =
        A.hom (pullback.fst A.hom B.hom p)
      exact CategoryTheory.congr_fun (pullback.condition : _ = _) p |>.symm
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : A.hom x = B.hom y := hx.trans hy.symm
    let p :=
      (TopCat.pullbackIsoProdSubtype A.hom B.hom).inv
        ⟨⟨x, y⟩, hxy⟩
    refine ⟨p, ?_⟩
    change A.hom (pullback.fst A.hom B.hom p) = z
    rw [TopCat.pullbackIsoProdSubtype_inv_fst_apply]
    exact hx

/-- The connectedness property seen by an approximation in the ambient plane. -/
def ImageConnected (A : Approximation) : Prop :=
  _root_.IsConnected (image A)

/-- The canonical morphism induced by an inclusion of subsets. -/
def ofSetHom {S T : Set ℂ} (hST : S ⊆ T) :
    ofSet S ⟶ ofSet T :=
  Over.homMk
    (TopCat.ofHom
      { toFun := fun z : S => ⟨z, hST z.property⟩
        continuous_toFun :=
          Continuous.subtype_mk continuous_subtype_val (fun z => hST z.property) })

theorem image_ofSet (S : Set ℂ) :
    image (ofSet S) = S := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩

theorem factorsThrough_ofSet_iff {S T : Set ℂ} :
    factorsThrough (ofSet S) (ofSet T) ↔ S ⊆ T := by
  constructor
  · rintro ⟨f⟩ z hz
    let x : S := ⟨z, hz⟩
    have hz' : z ∈ image (ofSet T) := by
      refine ⟨f.left x, ?_⟩
      calc
        (ofSet T).hom (f.left x) = (ofSet S).hom x := by
          exact CategoryTheory.congr_fun (Over.w f) x
        _ = z := rfl
    simpa [image_ofSet] using hz'
  · intro hST
    exact ⟨ofSetHom hST⟩

/-- A topology together with a strictly more demanding topology on the same carrier. -/
structure TopologyRefinement (X : Type*) where
  coarse : TopologicalSpace X
  fine : TopologicalSpace X
  fine_le_coarse : fine ≤ coarse

/-- The identity map from a finer topology to its coarser presentation. -/
def TopologyRefinement.fineToCoarse {X : Type*}
    (R : TopologyRefinement X) :
    @TopCat.of X R.fine ⟶ @TopCat.of X R.coarse :=
  @TopCat.ofHom X X R.fine R.coarse
    (@ContinuousMap.mk X X R.fine R.coarse id
      (continuous_iff_le_induced.mpr (by
        simpa only [induced_id] using R.fine_le_coarse)))

/-- A nested approximation tower, indexed from coarse to fine scales. -/
abbrev ApproximationTower :=
  ℕᵒᵖ ⥤ Approximation

/-- The universal limit approximation of a nested approximation tower. -/
def approximationTowerLimit (T : ApproximationTower) : Approximation :=
  limit T

/-- The limit cone for a nested approximation tower. -/
def approximationTowerLimitIsLimit (T : ApproximationTower) :
    IsLimit (limit.cone T) :=
  limit.isLimit T

end

end Categorical
end MLC
