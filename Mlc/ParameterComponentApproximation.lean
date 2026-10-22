import Mlc.FilledJuliaConnected
import Mlc.LocalConnectivity
import Mlc.CategoricalTopologicalApproximation
import Mlc.CategoricalMandelbrot

/-!
# Component neighborhoods and finite outer approximations

The frozen translated Green sublevels are not shrinking parameter
neighborhoods. This module replaces them with connected components of metric
balls and a finite-orbit outer approximation criterion. The latter is an
explicit sufficient input for Mandelbrot local connectedness; it is not
asserted unconditionally.
-/

namespace MLC
namespace ParameterComponent

open Set Filter Topology Metric

noncomputable section

variable {X : Type*} [MetricSpace X]

/-- The component of the radius `2⁻ⁿ` ball containing its center. -/
def dyadicComponent (x : X) (n : Nat) : Set X :=
  connectedComponentIn (ball x ((1 / 2 : Real) ^ n)) x

theorem dyadicComponent_connected (x : X) (n : Nat) :
    IsConnected (dyadicComponent x n) :=
  isConnected_connectedComponentIn_iff.mpr (mem_ball_self (by positivity))

/-- In a metric space, these components form a neighborhood basis exactly
    when the space is locally connected. -/
theorem locallyConnectedSpace_iff_dyadicComponent_mem_nhds :
    LocallyConnectedSpace X ↔
      ∀ (x : X) (n : Nat), dyadicComponent x n ∈ nhds x := by
  constructor
  · intro h
    letI : LocallyConnectedSpace X := h
    intro x n
    exact connectedComponentIn_mem_nhds (ball_mem_nhds x (by positivity))
  · intro h
    rw [locallyConnectedSpace_iff_connected_subsets]
    intro x U hU
    obtain ⟨n, _, hn⟩ :=
      (nhds_basis_ball_pow (by norm_num : (0 : Real) < 1 / 2)
        (by norm_num : (1 / 2 : Real) < 1)).mem_iff.mp hU
    exact ⟨dyadicComponent x n, h x n,
      isPreconnected_connectedComponentIn,
      (connectedComponentIn_subset _ _).trans hn⟩

/-- A connected component of a compact set is compact. -/
theorem isCompact_component {F : Set X} (hF : IsCompact F) {x : X}
    (hx : x ∈ F) : IsCompact (connectedComponentIn F x) := by
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- Components commute with decreasing intersections of compact sets that
    share a common point. -/
theorem component_iInter_eq
    (F : Nat → Set X) (hanti : Antitone F)
    (hcompact : ∀ n, IsCompact (F n)) (x : X) (hx : ∀ n, x ∈ F n) :
    connectedComponentIn (⋂ n, F n) x =
      ⋂ n, connectedComponentIn (F n) x := by
  apply Subset.antisymm
  · intro y hy
    exact mem_iInter.mpr fun n =>
      connectedComponentIn_mono x (iInter_subset F n) hy
  · have hpre :
        IsPreconnected (⋂ n, connectedComponentIn (F n) x) := by
      apply MLC.Quadratic.isPreconnected_iInter_of_sequence
      · intro n m hnm
        exact connectedComponentIn_mono x (hanti hnm)
      · intro n
        exact isCompact_component (hcompact n) (hx n)
      · intro n
        exact isPreconnected_connectedComponentIn
    apply hpre.subset_connectedComponentIn
    · exact mem_iInter.mpr fun n => mem_connectedComponentIn (hx n)
    · intro y hy
      exact mem_iInter.mpr fun n =>
        connectedComponentIn_subset (F n) x (mem_iInter.mp hy n)

/-- The component of a finite outer stage inside a closed metric ball. -/
def outerComponent (O : Nat → Set X) (x : X) (r : Real) (N : Nat) : Set X :=
  connectedComponentIn (O N ∩ closedBall x r) x

/-- Uniform finite-stage buffering of a neighborhood around every point. -/
def UniformOuterBuffer (S : Set X) (O : Nat → Set X) : Prop :=
  ∀ x ∈ S, ∀ ε > (0 : Real), ∃ r, 0 < r ∧ r < ε ∧
    ∃ δ, 0 < δ ∧ δ < r ∧
      ∀ N, ∃ L, N ≤ L ∧
        O L ∩ closedBall x δ ⊆ outerComponent O x r N

/-- A compact decreasing outer approximation plus `UniformOuterBuffer`
    yields local connectedness of its limit. -/
theorem locallyConnectedSpace_of_uniformOuterBuffer
    (S : Set X) (O : Nat → Set X) (hanti : Antitone O)
    (hcompact : ∀ N, IsCompact (O N)) (hlim : (⋂ N, O N) = S)
    (hbuffer : UniformOuterBuffer S O) :
    LocallyConnectedSpace S := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrε, δ, hδ, _, hcert⟩ := hbuffer x x.property ε hε
  have hSO : ∀ N, S ⊆ O N := by
    intro N
    rw [← hlim]
    exact iInter_subset O N
  let F : Nat → Set X := fun N => O N ∩ closedBall (x : X) r
  let D : Set X := ⋂ N, outerComponent O (x : X) r N
  have hxF : ∀ N, (x : X) ∈ F N := by
    intro N
    exact ⟨hSO N x.property, mem_closedBall_self (le_of_lt hr)⟩
  have hD_eq : D = connectedComponentIn (⋂ N, F N) (x : X) :=
    (component_iInter_eq F
      (fun _ _ h => inter_subset_inter_left _ (hanti h))
      (fun N => (hcompact N).inter_right isClosed_closedBall)
      (x : X) hxF).symm
  have hDconn : IsConnected D := by
    rw [hD_eq]
    exact isConnected_connectedComponentIn_iff.mpr (mem_iInter.mpr hxF)
  have hDS : D ⊆ S := by
    rw [← hlim]
    intro y hy
    exact mem_iInter.mpr fun N =>
      (connectedComponentIn_subset (F N) (x : X) (mem_iInter.mp hy N)).1
  have hDr : D ⊆ closedBall (x : X) r := by
    intro y hy
    exact (connectedComponentIn_subset (F 0) (x : X) (mem_iInter.mp hy 0)).2
  let V : Set S := Subtype.val ⁻¹' D
  have hVimage : (Subtype.val : S → X) '' V = D :=
    image_preimage_eq_of_subset (fun y hy => ⟨⟨y, hDS hy⟩, rfl⟩)
  refine ⟨V, ?_, ?_, ?_⟩
  · apply Filter.mem_of_superset (ball_mem_nhds x hδ)
    intro y hy
    apply mem_iInter.mpr
    intro N
    obtain ⟨L, _, hL⟩ := hcert N
    exact hL ⟨hSO L y.property, mem_closedBall.mpr (le_of_lt (mem_ball.mp hy))⟩
  · have hVconn : IsConnected V := by
      rw [← MLC.isConnected_subtype_val_image V, hVimage]
      exact hDconn
    exact hVconn.isPreconnected
  · intro y hy
    apply hεU
    exact lt_of_le_of_lt (hDr hy) hrε

/-- Categorical image connectedness for a dyadic component in a subspace. -/
theorem categorical_dyadicComponent_connected (S : Set Complex) (x : S) (n : Nat) :
    MLC.Categorical.ImageConnected
      (MLC.Categorical.ofSet
        ((Subtype.val : S → Complex) '' dyadicComponent x n)) := by
  change IsConnected (MLC.Categorical.image _)
  rw [MLC.Categorical.image_ofSet]
  exact (dyadicComponent_connected x n).image Subtype.val continuous_subtype_val.continuousOn

/-- The finite-orbit buffer condition for the Mandelbrot outer approximation. -/
def MandelbrotUniformOuterBuffer : Prop :=
  UniformOuterBuffer MLC.Quadratic.MandelbrotSet
    MLC.Categorical.Mandelbrot.outerOrbitSet

/-- Conditional root theorem supplied by the finite-orbit buffer input. -/
theorem mandelbrot_locallyConnected_of_uniformOuterBuffer
    (hbuffer : MandelbrotUniformOuterBuffer) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet :=
  locallyConnectedSpace_of_uniformOuterBuffer
    MLC.Quadratic.MandelbrotSet MLC.Categorical.Mandelbrot.outerOrbitSet
    (fun _ _ h => MLC.Categorical.Mandelbrot.outerOrbitSet_antitone h)
    MLC.Categorical.Mandelbrot.isCompact_outerOrbitSet
    MLC.Categorical.Mandelbrot.iInter_outerOrbitSet_eq_set hbuffer

#print axioms dyadicComponent_connected
#print axioms locallyConnectedSpace_iff_dyadicComponent_mem_nhds
#print axioms component_iInter_eq
#print axioms locallyConnectedSpace_of_uniformOuterBuffer
#print axioms categorical_dyadicComponent_connected
#print axioms mandelbrot_locallyConnected_of_uniformOuterBuffer

end

end ParameterComponent
end MLC
