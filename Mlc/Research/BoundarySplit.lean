import Mlc.GridCertificate
import Mlc.Research.CaseTree
import Mlc.Research.Dimension

/-!
# The boundary of `M` against families of smooth curves

The boundary of the Mandelbrot set has Hausdorff dimension `2` (Shishikura), while a `C¹` loop has
dimension at most `1` (`Dimension.lean`). A family of loops splits the boundary into the part that
the loops carry and the rest.

* **`wildPart E γ`** is `E ∖ ⋃ i, range (γ i)`: the part of `E` that the loops of the family miss.
  It depends on the family: for the empty family it is all of `E`.
* **Theorem `dimH_wildPart_eq`**: if `E` has dimension `d > 1`, its wild part has dimension `d`
  for every countable family of loops (countable stability of the Hausdorff dimension, with the
  dimension `≤ 1` of the loops).
* **Theorem `ShishikuraDimension.dimH_wildPart_eq_two`**: given Shishikura's theorem, the wild part
  of the boundary of `M` has dimension exactly `2` for every countable family of loops, so it is
  nonempty and uncountable (`wildPart_nonempty`, `not_countable_wildPart`).
* **The skeleton.** The boundary of a hyperbolic component is a Jordan curve, real-analytic away
  from its root, and a parameter with an indifferent cycle lies on the boundary of the hyperbolic
  component of the period of the cycle; so the parameters with an indifferent cycle (the roots, and
  the Siegel and Cremer parameters) lie on countably many images of the circle under real-analytic
  maps. This is a fact of the literature that is not formalized, and it enters as the hypothesis
  `hskel`: the family of loops covers the boundary parameters with an indifferent cycle
  (`HasIndifferentCycle`).
* **Theorem `ShishikuraDimension.dimH_noIndifferentCycle_eq_two`**: with `hskel`, the boundary
  parameters with no indifferent cycle have Hausdorff dimension `2`: the extra dimension of the
  boundary over the smooth curves lies in the parameters with no indifferent cycle.

The wild part is not the set of parameters of Problems 4.3 and 4.4. It depends on the family (a
larger family has a smaller wild part). The set of boundary parameters with no indifferent cycle
does not depend on any family, and it contains parameters for which MLC is known, the Misiurewicz
parameters (for example the end point `c = i` of a filament of `M`) among them.

* **Theorem `frontier_mandelbrot_eq_unresolved`**: the boundary is the set `R` of unresolved
  parameters of the grid certificate (`Mlc/GridCertificate.lean`). It is the same set for every
  depth of the grid, which lowers only the certified bound on its area; the wild part lies in it
  (`wildPart_subset_unresolved`).
* **Theorem `ShishikuraDimension.exists_class_dimH_eq_two`**: for every dictionary the classes of
  the boundary parameters partition the boundary into finitely many sets, so some class has
  dimension `2`; the dimension of a finite union is the largest of the dimensions of its parts (a
  `max`). This is a statement about the finite partition and holds for every dictionary, for
  example one that labels the whole boundary `neutral`; it says nothing about the dynamical
  classes. For the intended dictionary the parameters of the class `neutral` lie in the skeleton,
  of dimension at most `1`, so the dimension is carried by other classes, and which ones is
  undetermined here.
-/

namespace MLC.Research

open Set MeasureTheory

noncomputable section

deriving instance Fintype for BoundaryClass

/-- `c` has an **indifferent cycle**: `z² + c` has a periodic cycle whose multiplier has modulus
`1`. The parameters of the roots (parabolic), Siegel and Cremer cycles are of this kind. -/
def HasIndifferentCycle (c : ℂ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ z : ℂ, (MLC.Quadratic.fc c)^[n] z = z ∧
    ‖deriv ((MLC.Quadratic.fc c)^[n]) z‖ = 1

/-- The **wild part** of a set `E` relative to a family of `C¹` loops: the points of `E` that no
loop of the family passes through. -/
def wildPart {ι : Type*} (E : Set ℂ) (γ : ι → ℝ → ℂ) : Set ℂ :=
  E \ ⋃ i, range (γ i)

lemma wildPart_subset {ι : Type*} (E : Set ℂ) (γ : ι → ℝ → ℂ) : wildPart E γ ⊆ E :=
  diff_subset

/-- **The extra dimension lies off the loops.** If `E` has Hausdorff dimension `d > 1`, the part of
`E` outside countably many `C¹` loops has dimension `d`: the loops, of dimension at most `1`, carry
none of it. -/
theorem dimH_wildPart_eq {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ} (hγ : ∀ i, IsLoop (γ i))
    {E : Set ℂ} {d : ENNReal} (hd : 1 < d) (hE : dimH E = d) : dimH (wildPart E γ) = d := by
  refine le_antisymm (hE ▸ dimH_mono (wildPart_subset E γ)) ?_
  by_contra hlt
  have hsub : E ⊆ wildPart E γ ∪ ⋃ i, range (γ i) := fun x hx => by
    by_cases h : x ∈ ⋃ i, range (γ i)
    · exact Or.inr h
    · exact Or.inl ⟨hx, h⟩
  have h1 : dimH E ≤ max (dimH (wildPart E γ)) (dimH (⋃ i, range (γ i))) :=
    (dimH_mono hsub).trans_eq (dimH_union _ _)
  have h2 : dimH (⋃ i, range (γ i)) < d := (dimH_iUnion_range_le_one hγ).trans_lt hd
  have h3 : max (dimH (wildPart E γ)) (dimH (⋃ i, range (γ i))) < d :=
    max_lt (not_le.1 hlt) h2
  exact absurd (hE ▸ h1) (not_le.2 h3)

/-- The boundary of the Mandelbrot set is the set of unresolved parameters of the grid
certificate, `M ∖ int M`. -/
theorem frontier_mandelbrot_eq_unresolved :
    frontier MLC.Quadratic.MandelbrotSet = MLC.Certified.Unresolved := by
  rw [MLC.Quadratic.isClosed_mandelbrot.frontier_eq]
  rfl

/-- **The wild part lies in the unresolved set.** The unresolved set `R = M ∖ int M` of the grid
certificate is the same set for every depth of the grid, which lowers only the certified bound on
its area; the wild part of the boundary lies in it. -/
theorem wildPart_subset_unresolved {ι : Type*} (γ : ι → ℝ → ℂ) :
    wildPart (frontier MLC.Quadratic.MandelbrotSet) γ ⊆ MLC.Certified.Unresolved :=
  frontier_mandelbrot_eq_unresolved ▸ wildPart_subset _ γ

namespace ShishikuraDimension

variable (hS : ShishikuraDimension)
include hS

/-- **The wild part of the boundary has dimension `2`.** Outside any countable family of `C¹` loops,
the boundary of the Mandelbrot set keeps its whole Hausdorff dimension. -/
theorem dimH_wildPart_eq_two {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ}
    (hγ : ∀ i, IsLoop (γ i)) :
    dimH (wildPart (frontier MLC.Quadratic.MandelbrotSet) γ) = 2 :=
  dimH_wildPart_eq hγ (by norm_num) hS

/-- **The extra dimension lies in the parameters with no indifferent cycle.** If a countable family
of `C¹` loops covers the boundary parameters with an indifferent cycle (the skeleton: the boundaries
of the hyperbolic components, a published fact that is not formalized), the boundary parameters with
no indifferent cycle have Hausdorff dimension `2`. -/
theorem dimH_noIndifferentCycle_eq_two {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ}
    (hγ : ∀ i, IsLoop (γ i))
    (hskel : ∀ c ∈ frontier MLC.Quadratic.MandelbrotSet, HasIndifferentCycle c →
      c ∈ ⋃ i, range (γ i)) :
    dimH {c ∈ frontier MLC.Quadratic.MandelbrotSet | ¬ HasIndifferentCycle c} = 2 := by
  refine le_antisymm ((dimH_mono fun c hc => hc.1).trans_eq hS) ?_
  rw [← hS.dimH_wildPart_eq_two hγ]
  exact dimH_mono fun c hc => ⟨hc.1, fun hi => hc.2 (hskel c hc.1 hi)⟩

/-- The wild part of the boundary is nonempty. -/
theorem wildPart_nonempty {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ} (hγ : ∀ i, IsLoop (γ i)) :
    (wildPart (frontier MLC.Quadratic.MandelbrotSet) γ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have := hS.dimH_wildPart_eq_two hγ
  rw [h, dimH_empty] at this
  norm_num at this

/-- The wild part of the boundary is uncountable: a countable set has dimension `0`. -/
theorem not_countable_wildPart {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ}
    (hγ : ∀ i, IsLoop (γ i)) :
    ¬ (wildPart (frontier MLC.Quadratic.MandelbrotSet) γ).Countable := fun hc => by
  have := hS.dimH_wildPart_eq_two hγ
  rw [hc.dimH_zero] at this
  norm_num at this

/-- **The finite partition shares the dimension of the boundary.** For every dictionary, the boundary
is the union of the finitely many sets of its parameters of a given class, and the dimension of a
finite union is the largest of the dimensions of its parts, so some class has dimension `2`. The
statement concerns the finite partition only: it holds for a dictionary that labels the whole
boundary `neutral`, and says nothing about the dynamical classes. -/
theorem exists_class_dimH_eq_two (G : Geometry) :
    ∃ k : BoundaryClass,
      dimH {c ∈ frontier MLC.Quadratic.MandelbrotSet | G.cls c = k} = 2 := by
  have hU : frontier MLC.Quadratic.MandelbrotSet =
      ⋃ k : BoundaryClass, {c ∈ frontier MLC.Quadratic.MandelbrotSet | G.cls c = k} := by
    ext c
    simp
  have h2 : dimH (⋃ k : BoundaryClass,
      {c ∈ frontier MLC.Quadratic.MandelbrotSet | G.cls c = k}) = 2 := hU ▸ hS
  rw [dimH_iUnion] at h2
  haveI : Nonempty BoundaryClass := ⟨BoundaryClass.finite⟩
  obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite
    (f := fun k : BoundaryClass =>
      dimH {c ∈ frontier MLC.Quadratic.MandelbrotSet | G.cls c = k})
  exact ⟨k, hk.trans h2⟩

end ShishikuraDimension

end

end MLC.Research
