import Mlc.CertifiedOrbitApproximation

/-!
# Nested finite-cell addresses

An address is a compatible choice of one cell at every resolution.  The
compactness and vanishing-diameter theorem is independent of the particular
cell generator.  Surjectivity of the address map for a concrete generator is
therefore reduced to a finite covering proof.
-/

namespace MLC
namespace ParameterAddress

open Set Metric

noncomputable section

def Address (A : CertifiedOrbit.FiniteCellOuterApproximation) : Type :=
  {a : ∀ n, A.index n //
    ∀ n, A.cell (n + 1) (a (n + 1)) ⊆ A.cell n (a n)}

def addressCell (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) : Set ℂ :=
  A.cell n (a.1 n)

theorem address_cell_nonempty (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) :
    (addressCell A a n).Nonempty :=
  A.cell_nonempty n (a.1 n)

theorem address_cell_compact (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) :
    IsCompact (addressCell A a n) :=
  A.cell_compact n (a.1 n)

theorem address_cell_nested (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) :
    addressCell A a (n + 1) ⊆ addressCell A a n :=
  a.2 n

/-- A concrete address system must provide this vanishing-diameter estimate. -/
def VanishingDiameter (A : CertifiedOrbit.FiniteCellOuterApproximation) : Prop :=
  ∀ a : Address A, ∀ x y : ℂ,
    (∀ n, x ∈ addressCell A a n) →
    (∀ n, y ∈ addressCell A a n) →
    ∀ ε > (0 : ℝ), dist x y < ε

theorem address_intersection_nonempty
    (A : CertifiedOrbit.FiniteCellOuterApproximation) (a : Address A) :
    (⋂ n, addressCell A a n).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => addressCell A a n)
  · intro n
    exact address_cell_nested A a n
  · intro n
    exact address_cell_nonempty A a n
  · exact address_cell_compact A a 0
  · intro n
    exact (address_cell_compact A a n).isClosed

theorem address_intersection_subsingleton
    (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (hdiam : VanishingDiameter A) (a : Address A) :
    Set.Subsingleton (⋂ n, addressCell A a n) := by
  intro x hx y hy
  apply eq_of_forall_dist_le
  intro ε hε
  exact (hdiam a x y
    (fun n => mem_iInter.mp hx n)
    (fun n => mem_iInter.mp hy n) ε hε).le

theorem address_intersection_singleton
    (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (hdiam : VanishingDiameter A) (a : Address A) :
    ∃! x : ℂ, ∀ n, x ∈ addressCell A a n := by
  obtain ⟨x, hx⟩ := address_intersection_nonempty A a
  refine ⟨x, (fun n => mem_iInter.mp hx n), ?_⟩
  intro y hy
  exact (address_intersection_subsingleton A hdiam
    a hx (mem_iInter.mpr hy)).symm

/-! ## Coverage and the address map

The following proposition is the exact finite-cover obligation for a concrete
dyadic or CAD cell generator. -/

def AddressCoverage (A : CertifiedOrbit.FiniteCellOuterApproximation) : Prop :=
  ∀ c ∈ MLC.Categorical.Mandelbrot.set,
    ∃ a : Address A, ∀ n, c ∈ addressCell A a n

theorem address_point_mem_mandelbrot
    (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (x : ℂ)
    (hx : ∀ n, x ∈ addressCell A a n) :
    x ∈ MLC.Categorical.Mandelbrot.set := by
  rw [← CertifiedOrbit.iInter_stage_eq_mandelbrot A]
  refine mem_iInter.mpr ?_
  intro n
  exact mem_iUnion.mpr ⟨a.1 n, hx n⟩

theorem address_point_unique
    (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (hdiam : VanishingDiameter A) (a : Address A)
    {x y : ℂ}
    (hx : ∀ n, x ∈ addressCell A a n)
    (hy : ∀ n, y ∈ addressCell A a n) :
    x = y :=
  address_intersection_subsingleton A hdiam a
    (mem_iInter.mpr hx) (mem_iInter.mpr hy)

end
end ParameterAddress
end MLC
