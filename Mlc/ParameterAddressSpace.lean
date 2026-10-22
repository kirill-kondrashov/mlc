import Mlc.CertifiedOrbitApproximation

/-!
# Nested finite-cell addresses

An address is a compatible choice of one nonempty cell at every resolution.
The compactness and vanishing-diameter theorem is independent of the
particular cell generator. Surjectivity of the address map for a concrete
generator is therefore reduced to a covering proof.
-/

namespace MLC
namespace ParameterAddress

open Set Metric

noncomputable section

def Address (A : CertifiedOrbit.FiniteCellOuterApproximation) : Type :=
  {a : ∀ n, A.index n //
    (∀ n, A.cell (n + 1) (a (n + 1)) ⊆ A.cell n (a n)) ∧
      (∀ n, (A.cell n (a n)).Nonempty)}

def addressCell (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) : Set ℂ :=
  A.cell n (a.1 n)

theorem address_cell_nonempty (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) :
    (addressCell A a n).Nonempty :=
  a.2.2 n

theorem address_cell_compact (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) :
    IsCompact (addressCell A a n) :=
  A.cell_compact n (a.1 n)

theorem address_cell_nested (A : CertifiedOrbit.FiniteCellOuterApproximation)
    (a : Address A) (n : ℕ) :
    addressCell A a (n + 1) ⊆ addressCell A a n :=
  a.2.1 n

/-- A concrete address system must provide this vanishing-diameter estimate. -/
def VanishingDiameter (A : CertifiedOrbit.FiniteCellOuterApproximation) : Prop :=
  ∀ a : Address A, ∀ x y : ℂ,
    (∀ n, x ∈ addressCell A a n) →
    (∀ n, y ∈ addressCell A a n) →
    ∀ ε > (0 : ℝ), dist x y < ε

theorem dyadicGridOuterApproximation_vanishingDiameter :
    VanishingDiameter CertifiedOrbit.dyadicGridOuterApproximation := by
  intro a x y hx hy ε hε
  obtain ⟨n, hn⟩ :=
    CertifiedOrbit.exists_dyadicRadius_lt (by positivity : 0 < ε / 8)
  have hxbox : x ∈ CertifiedOrbit.dyadicGridBox n
      (a.1 n).1 (a.1 n).2 := by
    have hxn := hx n
    change x ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n ∩
      CertifiedOrbit.dyadicGridBox n (a.1 n).1 (a.1 n).2 at hxn
    exact hxn.2
  have hybox : y ∈ CertifiedOrbit.dyadicGridBox n
      (a.1 n).1 (a.1 n).2 := by
    have hyn := hy n
    change y ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n ∩
      CertifiedOrbit.dyadicGridBox n (a.1 n).1 (a.1 n).2 at hyn
    exact hyn.2
  exact (CertifiedOrbit.dist_le_dyadicGridBox n (a.1 n).1 (a.1 n).2
    hxbox hybox).trans_lt (by nlinarith)

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

theorem dyadicGridOuterApproximation_addressCoverage :
    AddressCoverage CertifiedOrbit.dyadicGridOuterApproximation := by
  intro c hc
  let a : ∀ n, CertifiedOrbit.dyadicGridOuterApproximation.index n :=
    fun n =>
      (CertifiedOrbit.dyadicGridCoordinateIndex n c.re,
        CertifiedOrbit.dyadicGridCoordinateIndex n c.im)
  have hnorm : ‖c‖ ≤ 2 :=
    (MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet 0 hc).1
  have hre := abs_le.mp ((Complex.abs_re_le_norm c).trans hnorm)
  have him := abs_le.mp ((Complex.abs_im_le_norm c).trans hnorm)
  have hcell : ∀ n,
      c ∈ CertifiedOrbit.dyadicGridOuterApproximation.cell n (a n) := by
    intro n
    have houter := MLC.Categorical.Mandelbrot.set_subset_outerOrbitSet n hc
    obtain ⟨hrel, hreu⟩ :=
      CertifiedOrbit.dyadicGridCoordinateIndex_mem n hre.1 hre.2
    obtain ⟨himl, himu⟩ :=
      CertifiedOrbit.dyadicGridCoordinateIndex_mem n him.1 him.2
    change c ∈ MLC.Categorical.Mandelbrot.outerOrbitSet n ∩
      CertifiedOrbit.dyadicGridBox n (a n).1 (a n).2
    exact ⟨houter, hrel, hreu, himl, himu⟩
  have hparent : ∀ n,
      (a (n + 1)).1.val / 2 = (a n).1.val ∧
        (a (n + 1)).2.val / 2 = (a n).2.val := by
    intro n
    dsimp [a]
    exact
      ⟨CertifiedOrbit.dyadicGridCoordinateIndex_parent n hre.1 hre.2,
        CertifiedOrbit.dyadicGridCoordinateIndex_parent n him.1 him.2⟩
  have hnest : ∀ n,
      CertifiedOrbit.dyadicGridOuterApproximation.cell (n + 1) (a (n + 1)) ⊆
        CertifiedOrbit.dyadicGridOuterApproximation.cell n (a n) := by
    intro n z hz
    change z ∈ MLC.Categorical.Mandelbrot.outerOrbitSet (n + 1) ∩
      CertifiedOrbit.dyadicGridBox (n + 1) (a (n + 1)).1 (a (n + 1)).2 at hz
    obtain ⟨hparentRe, hparentIm⟩ := hparent n
    have houter :=
      MLC.Categorical.Mandelbrot.outerOrbitSet_antitone (Nat.le_succ n) hz.1
    have hbox := CertifiedOrbit.dyadicGridBox_succ_subset n
      (a n).1 (a n).2 (a (n + 1)).1 (a (n + 1)).2
      hparentRe hparentIm hz.2
    exact ⟨houter, hbox⟩
  have hnonempty : ∀ n,
      (CertifiedOrbit.dyadicGridOuterApproximation.cell n (a n)).Nonempty :=
    fun n => ⟨c, hcell n⟩
  refine ⟨⟨a, hnest, hnonempty⟩, ?_⟩
  intro n
  exact hcell n

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
