import Mlc.CategoricalTopologicalApproximation
import Mlc.ParaPuzzleConnectivity
import Molecule.Mol
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

/-- The ordinary subspace approximation carried by the whole Mandelbrot set. -/
def setApproximation : Approximation :=
  ofSet set

/-! ## A two-sided orbit approximation

The outer and inner systems below encode different finite information. An
outer stage checks only a finite prefix of the critical orbit against the
universal escape radius `2`; an inner stage supplies one uniform bound for the
entire critical orbit. The former is a decreasing finite-observation system,
while the latter is an increasing witness system. Their limits agree with the
Mandelbrot set for different reasons.
-/

/-- A two-sided approximation of a fixed subset of the parameter plane. -/
structure TwoSidedSetApproximation (S : Set ℂ) where
  inner : ℕ → Set ℂ
  outer : ℕ → Set ℂ
  inner_mono : ∀ {n m}, n ≤ m → inner n ⊆ inner m
  outer_antitone : ∀ {n m}, n ≤ m → outer m ⊆ outer n
  inner_subset : ∀ n, inner n ⊆ S
  subset_outer : ∀ n, S ⊆ outer n
  inner_limit : ⋃ n, inner n = S
  outer_limit : ⋂ n, outer n = S

theorem TwoSidedSetApproximation.isConnected_of_inner
    {S : Set ℂ} (A : TwoSidedSetApproximation S)
    (h_conn : ∀ n, IsConnected (A.inner n))
    (h_common : ∃ x, ∀ n, x ∈ A.inner n) :
    IsConnected S := by
  rw [← A.inner_limit]
  rcases h_common with ⟨x, hx⟩
  refine ⟨⟨x, Set.mem_iUnion.mpr ⟨0, hx 0⟩⟩, ?_⟩
  exact isPreconnected_iUnion ⟨x, Set.mem_iInter.mpr hx⟩
    (fun n => (h_conn n).isPreconnected)

theorem TwoSidedSetApproximation.isPreconnected_of_outer
    {S : Set ℂ} (A : TwoSidedSetApproximation S)
    (h_compact : ∀ n, IsCompact (A.outer n))
    (h_pre : ∀ n, IsPreconnected (A.outer n)) :
    IsPreconnected S := by
  rw [← A.outer_limit]
  apply MLC.Quadratic.isPreconnected_iInter_of_sequence
  · intro n m h
    exact A.outer_antitone h
  · exact h_compact
  · exact h_pre

/-- Inner approximants: one natural uniform bound controls the whole critical
    orbit. These form an increasing exhaustion because every bounded orbit has
    a natural bound above one of its real bounds. -/
def innerOrbitSet (N : ℕ) : Set ℂ :=
  {c | ∀ n, ‖MLC.Quadratic.orbit c 0 n‖ ≤ (N : ℝ)}

/-- Outer approximants: the parameter is in the universal disk and only the
    first `N` critical-orbit observations are required to stay inside the
    universal radius `2`. -/
def outerOrbitSet (N : ℕ) : Set ℂ :=
  {c | ‖c‖ ≤ (2 : ℝ) ∧
    ∀ n ≤ N, ‖MLC.Quadratic.orbit c 0 n‖ ≤ (2 : ℝ)}

lemma zero_mem_innerOrbitSet (N : ℕ) :
    (0 : ℂ) ∈ innerOrbitSet N := by
  intro n
  have horbit :
      MLC.Quadratic.orbit (0 : ℂ) 0 n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [MLC.Quadratic.orbit_succ, ih]
        simp [MLC.Quadratic.fc]
  rw [horbit]
  exact_mod_cast (Nat.zero_le N)

lemma innerOrbitSet_mono {n m : ℕ} (h : n ≤ m) :
    innerOrbitSet n ⊆ innerOrbitSet m := by
  intro c hc k
  change ∀ k, ‖MLC.Quadratic.orbit c 0 k‖ ≤ (n : ℝ) at hc
  exact le_trans (hc k) (by exact_mod_cast h)

lemma outerOrbitSet_antitone {n m : ℕ} (h : n ≤ m) :
    outerOrbitSet m ⊆ outerOrbitSet n := by
  intro c hc
  change ‖c‖ ≤ (2 : ℝ) ∧
    (∀ k ≤ m, ‖MLC.Quadratic.orbit c 0 k‖ ≤ (2 : ℝ)) at hc
  refine ⟨hc.1, ?_⟩
  intro k hk
  exact hc.2 k (hk.trans h)

lemma innerOrbitSet_subset_set (N : ℕ) :
    innerOrbitSet N ⊆ set := by
  intro c hc
  change ∃ B : ℝ, ∀ n, ‖MLC.Quadratic.orbit c 0 n‖ ≤ B
  exact ⟨(N : ℝ), hc⟩

lemma set_subset_outerOrbitSet (N : ℕ) :
    set ⊆ outerOrbitSet N := by
  intro c hc
  have hc_ball : ‖c‖ ≤ (2 : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (Molecule.mandelbrot_subset_ball hc)
  have hc' :
      c ∈ ⋂ n, {c : ℂ | ‖MLC.Quadratic.orbit c 0 n‖ ≤ (2 : ℝ)} := by
    rw [← Molecule.mandelbrot_eq_inter]
    exact hc
  refine ⟨hc_ball, ?_⟩
  intro n hn
  exact Set.mem_iInter.mp hc' n

lemma isClosed_outerOrbitSet (N : ℕ) :
    IsClosed (outerOrbitSet N) := by
  let U : Set ℂ :=
    ⋂ n, ⋂ (_h : n ≤ N),
      {c : ℂ | ‖MLC.Quadratic.orbit c 0 n‖ ≤ (2 : ℝ)}
  have hU : IsClosed U := by
    dsimp [U]
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro hn
    exact isClosed_le
      (continuous_norm.comp (Molecule.continuous_orbit n)) continuous_const
  have h_eq :
      outerOrbitSet N = {c : ℂ | ‖c‖ ≤ (2 : ℝ)} ∩ U := by
    ext c
    simp [outerOrbitSet, U]
  rw [h_eq]
  exact (isClosed_le continuous_norm continuous_const).inter hU

lemma isCompact_outerOrbitSet (N : ℕ) :
    IsCompact (outerOrbitSet N) := by
  have h_closed := isClosed_outerOrbitSet N
  have h_subset :
      outerOrbitSet N ⊆ Metric.closedBall (0 : ℂ) 2 := by
    intro c hc
    exact (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hc.1)
  exact (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    h_closed h_subset

theorem iUnion_innerOrbitSet_eq_set :
    (⋃ N, innerOrbitSet N) = set := by
  ext c
  constructor
  · intro hc
    rcases Set.mem_iUnion.mp hc with ⟨N, hN⟩
    exact innerOrbitSet_subset_set N hN
  · intro hc
    change ∃ B : ℝ, ∀ n, ‖MLC.Quadratic.orbit c 0 n‖ ≤ B at hc
    rcases hc with ⟨B, hB⟩
    obtain ⟨N, hN⟩ := exists_nat_ge B
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    intro n
    exact le_trans (hB n) hN

theorem iInter_outerOrbitSet_eq_set :
    (⋂ N, outerOrbitSet N) = set := by
  ext c
  constructor
  · intro hc
    change c ∈ MLC.Quadratic.MandelbrotSet
    rw [Molecule.mandelbrot_eq_inter]
    refine Set.mem_iInter.mpr ?_
    intro n
    exact (Set.mem_iInter.mp hc n).2 n le_rfl
  · intro hc
    change c ∈ MLC.Quadratic.MandelbrotSet at hc
    have hc' :
        c ∈ ⋂ n, {c : ℂ | ‖MLC.Quadratic.orbit c 0 n‖ ≤ (2 : ℝ)} := by
      rw [← Molecule.mandelbrot_eq_inter]
      exact hc
    have hc_ball : ‖c‖ ≤ (2 : ℝ) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        (Molecule.mandelbrot_subset_ball hc)
    refine Set.mem_iInter.mpr ?_
    intro N
    change ‖c‖ ≤ (2 : ℝ) ∧
      ∀ n ≤ N, ‖MLC.Quadratic.orbit c 0 n‖ ≤ (2 : ℝ)
    refine ⟨hc_ball, ?_⟩
    intro n hn
    exact Set.mem_iInter.mp hc' n

/-- The concrete two-sided orbit approximation of the Mandelbrot set. -/
def mandelbrotTwoSidedApproximation :
    TwoSidedSetApproximation set where
  inner := innerOrbitSet
  outer := outerOrbitSet
  inner_mono := by
    intro n m h
    exact innerOrbitSet_mono h
  outer_antitone := by
    intro n m h
    exact outerOrbitSet_antitone h
  inner_subset := innerOrbitSet_subset_set
  subset_outer := set_subset_outerOrbitSet
  inner_limit := iUnion_innerOrbitSet_eq_set
  outer_limit := iInter_outerOrbitSet_eq_set

theorem isConnected_set_of_innerOrbitConnected
    (h_conn : ∀ N, IsConnected (innerOrbitSet N)) :
    IsConnected set := by
  apply TwoSidedSetApproximation.isConnected_of_inner
    mandelbrotTwoSidedApproximation h_conn
  exact ⟨0, zero_mem_innerOrbitSet⟩

theorem isPreconnected_set_of_outerOrbitPreconnected
    (h_pre : ∀ N, IsPreconnected (outerOrbitSet N)) :
    IsPreconnected set := by
  apply TwoSidedSetApproximation.isPreconnected_of_outer
    mandelbrotTwoSidedApproximation
  · exact isCompact_outerOrbitSet
  · exact h_pre

/-- The inner approximation as an object over the parameter plane. -/
def innerOrbitApproximation (N : ℕ) : Approximation :=
  ofSet (innerOrbitSet N)

/-- The outer approximation as an object over the parameter plane. -/
def outerOrbitApproximation (N : ℕ) : Approximation :=
  ofSet (outerOrbitSet N)

/-- The concrete set-level limit of the inner categorical approximations. -/
def innerOrbitLimitApproximation : Approximation :=
  ofSet (⋃ N, innerOrbitSet N)

/-- The concrete set-level limit of the outer categorical approximations. -/
def outerOrbitLimitApproximation : Approximation :=
  ofSet (⋂ N, outerOrbitSet N)

theorem image_innerOrbitLimitApproximation :
    image innerOrbitLimitApproximation = set := by
  rw [innerOrbitLimitApproximation, image_ofSet, iUnion_innerOrbitSet_eq_set]

theorem image_outerOrbitLimitApproximation :
    image outerOrbitLimitApproximation = set := by
  rw [outerOrbitLimitApproximation, image_ofSet, iInter_outerOrbitSet_eq_set]

/-- The finite-level inner approximation maps into the Mandelbrot object. -/
def innerOrbitToMandelbrot (N : ℕ) :
    innerOrbitApproximation N ⟶ setApproximation :=
  ofSetHom (innerOrbitSet_subset_set N)

/-- The Mandelbrot object maps into every finite-level outer approximation. -/
def mandelbrotToOuterOrbit (N : ℕ) :
    setApproximation ⟶ outerOrbitApproximation N :=
  ofSetHom (set_subset_outerOrbitSet N)

theorem innerOrbitApproximation_sandwich (N : ℕ) :
    Nonempty (innerOrbitApproximation N ⟶ setApproximation) ∧
      Nonempty (setApproximation ⟶ outerOrbitApproximation N) :=
  ⟨⟨innerOrbitToMandelbrot N⟩, ⟨mandelbrotToOuterOrbit N⟩⟩

theorem innerOrbitApproximation_step (N : ℕ) :
    Nonempty (innerOrbitApproximation N ⟶ innerOrbitApproximation (N + 1)) :=
  ⟨ofSetHom (innerOrbitSet_mono (Nat.le_succ N))⟩

theorem outerOrbitApproximation_step (N : ℕ) :
    Nonempty (outerOrbitApproximation (N + 1) ⟶ outerOrbitApproximation N) :=
  ⟨ofSetHom (outerOrbitSet_antitone (Nat.le_succ N))⟩

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
