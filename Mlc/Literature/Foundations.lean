import Mlc.CategoricalMandelbrot
import Mlc.Literature.Review
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Foundational objects used by the literature review

This file gives the review vocabulary stable Lean names.  The declarations
are deliberately thin wrappers around the existing quadratic-dynamics library
and generic topological interfaces; they do not assert the missing
phase--parameter or renormalization theorems.
-/

namespace MLC
namespace Literature

open Filter Set Topology

noncomputable section

/-- The quadratic polynomial in the review notation. -/
abbrev quadraticMap (c : ℂ) : ℂ → ℂ :=
  MLC.Quadratic.fc c

/-- The orbit used throughout the review. -/
abbrev quadraticOrbit (c z : ℂ) (n : ℕ) : ℂ :=
  MLC.Quadratic.orbit c z n

/-- The filled Julia set in the review notation. -/
abbrev filledJuliaSet (c : ℂ) : Set ℂ :=
  MLC.Quadratic.K c

/-- The Julia set in the review notation. -/
abbrev juliaSet (c : ℂ) : Set ℂ :=
  MLC.Quadratic.J c

/-- The Mandelbrot set in the review notation. -/
abbrev reviewMandelbrotSet : Set ℂ :=
  MLC.Quadratic.MandelbrotSet

theorem criticalOrbit_iff_mandelbrot (c : ℂ) :
    c ∈ reviewMandelbrotSet ↔
      ∃ B : ℝ, ∀ n, ‖quadraticOrbit c 0 n‖ ≤ B :=
  Iff.rfl

theorem filledJulia_iff_bounded_orbit (c z : ℂ) :
    z ∈ filledJuliaSet c ↔
      ∃ B : ℝ, ∀ n, ‖quadraticOrbit c z n‖ ≤ B :=
  Iff.rfl

/-- A nested connected neighborhood basis at one point. -/
structure ConnectedNeighborhoodBasis
    (X : Type*) [TopologicalSpace X] (x : X) where
  piece : ℕ → Set X
  piece_nhds : ∀ n, piece n ∈ 𝓝 x
  piece_preconnected : ∀ n, IsPreconnected (piece n)
  piece_subset : ∀ U ∈ 𝓝 x, ∃ n, piece n ⊆ U

theorem ConnectedNeighborhoodBasis.locallyConnectedAt
    {X : Type*} [TopologicalSpace X] {x : X}
    (B : ConnectedNeighborhoodBasis X x) :
    LocallyConnectedAt X x := by
  intro U hU
  obtain ⟨n, hn⟩ := B.piece_subset U hU
  exact ⟨B.piece n, B.piece_nhds n, B.piece_preconnected n, hn⟩

/-- A connected shrinking basis for the Mandelbrot parameter plane. -/
structure ParameterPuzzleBasis
    (c : ℂ) (hc : c ∈ reviewMandelbrotSet) where
  piece : ℕ → Set ℂ
  open_piece : ∀ n, IsOpen (piece n)
  connected_piece :
    ∀ n, IsConnected (piece n ∩ reviewMandelbrotSet)
  contains_parameter :
    ∀ n, c ∈ piece n
  basis :
    ∀ U ∈ 𝓝 c, ∃ n, piece n ⊆ U
  nested :
    ∀ n, piece (n + 1) ⊆ piece n
  singleton_intersection :
    (⋂ n, piece n) = {c}

/-- The phase from a shrinking parameter puzzle to a local basis. -/
def ParameterPuzzleBasis.realized
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (B : ParameterPuzzleBasis c hc) :
    ConnectedNeighborhoodBasis reviewMandelbrotSet ⟨c, hc⟩ where
  piece n := {x : reviewMandelbrotSet | x.1 ∈ B.piece n}
  piece_nhds := by
    intro n
    exact (isOpen_induced_iff.mpr ⟨B.piece n, B.open_piece n, rfl⟩).mem_nhds
      (B.contains_parameter n)
  piece_preconnected := by
    intro n
    let V : Set reviewMandelbrotSet :=
      {x : reviewMandelbrotSet | x.1 ∈ B.piece n}
    have himage :
        (Subtype.val : reviewMandelbrotSet → ℂ) '' V =
          B.piece n ∩ reviewMandelbrotSet := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.property⟩
      · rintro ⟨hz, hzM⟩
        exact ⟨⟨z, hzM⟩, hz, rfl⟩
    have hconn_image : IsConnected
        ((Subtype.val : reviewMandelbrotSet → ℂ) '' V) := by
      rw [himage]
      exact B.connected_piece n
    exact ((MLC.isConnected_subtype_val_image V).mp hconn_image).isPreconnected
  piece_subset := by
    intro U hU
    obtain ⟨V, hVU, hVopen, hcV⟩ := mem_nhds_iff.mp hU
    obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp hVopen
    rw [← hW] at hcV hVU
    have hcW : c ∈ W := hcV
    obtain ⟨n, hn⟩ := B.basis W (hWopen.mem_nhds hcW)
    refine ⟨n, ?_⟩
    intro x hx
    apply hVU
    change (x : ℂ) ∈ W
    exact hn hx

theorem localConnectivity_of_parameterPuzzleBasis
    {c : ℂ} {hc : c ∈ reviewMandelbrotSet}
    (B : ParameterPuzzleBasis c hc) :
    MandelbrotLocallyConnectedAt c hc :=
  B.realized.locallyConnectedAt

/-- The qualitative renormalization classes used by the review ledger. -/
inductive RenormalizationClass
  | primitive
  | satellite
  | neutral
  | parabolicallyBoundedPrimitive
  deriving Repr, DecidableEq

/-- A generic a-priori-bound interface for a renormalization tower. -/
structure APrioriBounds (Tower : Type*) where
  modulus : Tower → ℕ → ℝ
  lower_bound : ℝ
  lower_bound_pos : 0 < lower_bound
  modulus_ge : ∀ T n, lower_bound ≤ modulus T n

/-- The theorem-level shape of a geometric input that produces MLC at a
parameter class. -/
structure RenormalizationMLCInterface where
  parameterClass : ℂ → Prop
  result : PointwiseMLCResult parameterClass

end

end Literature
end MLC
