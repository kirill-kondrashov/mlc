import Mlc.CategoricalRoot
import Mlc.CertifiedOrbitApproximation
import Mlc.CertifiedTrappingRegions

/-!
# Finite component certificates

`FiniteComponentCriterion` is the finite-cover form of the outer-buffer
obligation.  Its fields are concrete certificate obligations; the implication
to `UniformOuterBuffer` is proved here.  No inhabitant of the criterion is
declared.
-/

namespace MLC
namespace FiniteComponent

open Set Metric

noncomputable section

abbrev outerSet : ℕ → Set ℂ :=
  MLC.Categorical.Mandelbrot.outerOrbitSet

abbrev outerComponent (c : ℂ) (r : ℝ) (N : ℕ) : Set ℂ :=
  MLC.ParameterComponent.outerComponent outerSet c r N

structure LocalPiece (k : ℕ) where
  inner : CertifiedTrapping.RationalBox
  r : ℝ
  δ : ℝ
  r_pos : 0 < r
  r_small : r < CertifiedOrbit.dyadicRadius k
  δ_pos : 0 < δ
  δ_lt_r : δ < r
  control :
    ∀ c ∈ MLC.Categorical.Mandelbrot.set, c ∈ inner.toSet →
      ∀ N, ∃ L, N ≤ L ∧
        outerSet L ∩ closedBall c δ ⊆ outerComponent c r N

structure CoverCertificate (k : ℕ) where
  indices : Finset ℕ
  piece : ℕ → LocalPiece k
  cover :
    ∃ T, outerSet T ⊆ ⋃ i ∈ indices, (piece i).inner.toSet

def FiniteComponentCriterion : Prop :=
  ∀ k, Nonempty (CoverCertificate k)

theorem uniformOuterBuffer_of_finiteComponentCriterion
    (h : FiniteComponentCriterion) :
    MLC.ParameterComponent.MandelbrotUniformOuterBuffer := by
  intro c hc ε hε
  obtain ⟨k, hk⟩ := CertifiedOrbit.exists_dyadicRadius_lt hε
  obtain ⟨certificate⟩ := h k
  obtain ⟨T, hcover⟩ := certificate.cover
  have hcT :
      c ∈ outerSet T :=
    MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet T hc
  have hcCover :
      c ∈ ⋃ i ∈ certificate.indices, (certificate.piece i).inner.toSet :=
    hcover hcT
  rcases mem_iUnion.mp hcCover with ⟨i, hcCover⟩
  rcases mem_iUnion.mp hcCover with ⟨hi, hci⟩
  let P := certificate.piece i
  refine ⟨P.r, P.r_pos, lt_trans P.r_small hk, P.δ, P.δ_pos, P.δ_lt_r, ?_⟩
  exact P.control c hc hci

theorem rootInput_of_finiteComponentCriterion
    (h : FiniteComponentCriterion) : MLC.RootInput :=
  ⟨uniformOuterBuffer_of_finiteComponentCriterion h⟩

end
end FiniteComponent
end MLC
