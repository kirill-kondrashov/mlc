import Mlc.CategoricalTopologicalApproximation
import Mlc.ParaPuzzleConnectivity
import Yoccoz.Quadratic.Complex.Basic
import Mathlib.Topology.Basic

namespace MLC
namespace Categorical
namespace Mandelbrot

open CategoryTheory CategoryTheory.Limits Set Topology

noncomputable section

/-- The Mandelbrot set as a subset of the ambient parameter plane. -/
abbrev set : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

/-- The topological boundary of the Mandelbrot set. -/
def boundary : Set ℂ :=
  frontier set

/-- The subspace topology carried by the boundary. -/
abbrev boundarySubspaceTopology : TopologicalSpace boundary :=
  inferInstance

/-- The interior approximation carried by the Mandelbrot set. -/
def insideApproximation : Approximation :=
  ofSet (interior set)

/-- The ordinary subspace approximation carried by the Mandelbrot boundary. -/
def boundaryApproximation : Approximation :=
  Over.mk
    (@TopCat.ofHom boundary ℂ boundarySubspaceTopology inferInstance
      (@ContinuousMap.mk boundary ℂ boundarySubspaceTopology inferInstance
        (fun z => (z : ℂ)) continuous_subtype_val))

/-- The ordinary subspace approximation carried by the whole Mandelbrot set. -/
def setApproximation : Approximation :=
  ofSet set

theorem image_insideApproximation :
    image insideApproximation = interior set :=
  image_ofSet _

theorem image_boundaryApproximation :
    image boundaryApproximation = boundary :=
  image_ofSet _

theorem image_setApproximation :
    image setApproximation = set :=
  image_ofSet _

lemma paraPuzzlePiece_nested_le (c : ℂ) {n m : ℕ} (h : n ≤ m) :
    MLC.Quadratic.ParaPuzzlePieceAt c m ⊆ MLC.Quadratic.ParaPuzzlePieceAt c n := by
  refine Nat.le_induction (m := n) (n := m) ?_ ?_ h
  · exact Subset.rfl
  · intro k _hk ih
    exact (MLC.Quadratic.para_puzzle_piece_nested c k).trans ih

/-- The nested parameter-puzzle approximations as an opposite-indexed
    diagram in the over-category. -/
def parameterApproximationTower (c : ℂ) : ApproximationTower where
  obj n := ofSet (MLC.Quadratic.ParaPuzzlePieceAt c n.unop)
  map {n m} f :=
    ofSetHom (paraPuzzlePiece_nested_le c (CategoryTheory.le_of_op_hom f))
  map_id := by
    intro n
    apply Over.OverMorphism.ext
    rfl
  map_comp := by
    intro n m k f g
    apply Over.OverMorphism.ext
    rfl

/-- The universal categorical approximation obtained from all parameter
    puzzle levels. -/
def parameterApproximationLimit (c : ℂ) : Approximation :=
  approximationTowerLimit (parameterApproximationTower c)

/-- The universal property of the parameter-puzzle approximation limit. -/
def parameterApproximationLimitIsLimit (c : ℂ) :
    IsLimit (limit.cone (parameterApproximationTower c)) :=
  approximationTowerLimitIsLimit (parameterApproximationTower c)

/-- A deliberately finer topology on the boundary carrier. -/
structure BoundaryTopology where
  topology : TopologicalSpace boundary
  fine_le_subspace : topology ≤ boundarySubspaceTopology
  continuous_inclusion :
    @Continuous boundary ℂ topology inferInstance (fun z => (z : ℂ))

/-- The boundary approximation equipped with a chosen finer topology. -/
def boundaryWithTopology (B : BoundaryTopology) : Approximation :=
  Over.mk
    (@TopCat.ofHom boundary ℂ B.topology inferInstance
      (@ContinuousMap.mk boundary ℂ B.topology inferInstance
        (fun z => (z : ℂ)) B.continuous_inclusion))

/-- The finer boundary presentation continuously maps to the ordinary
    subspace presentation. -/
def boundaryToSubspace (B : BoundaryTopology) :
    boundaryWithTopology B ⟶ boundaryApproximation :=
  Over.homMk
    (TopologyRefinement.fineToCoarse
      { coarse := boundarySubspaceTopology
        fine := B.topology
        fine_le_coarse := B.fine_le_subspace }) (by
      ext z
      rfl)

theorem boundaryToSubspace_is_identity_on_points (B : BoundaryTopology)
    (z : boundary) :
    (boundaryToSubspace B).left z = z := by
  change id z = z
  rfl

end

end Mandelbrot
end Categorical
end MLC
