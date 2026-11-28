import Mlc.Research.PhaseParameter
import Mlc.Research.QuasiInvariance
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Fractal dimension against smooth curves

The moduli of this development are measured with `C¹` loops, curves of Hausdorff dimension at most
`1`, while the sets that they go around (the Julia sets, the Mandelbrot set, the fibers of a nest)
are fractals: the boundary of the Mandelbrot set has topological dimension `1` and Hausdorff
dimension `2` (Shishikura, 1998). A fractal holds more dimension than any piecewise smooth curve. This
module expresses that difference in Lean, together with the statements that follow from it for the
objects of the programme.

* **Smooth curves are thin** (`IsLoop.dimH_range_le`, `dimH_iUnion_range_le_one`): the image of a
  `C¹` loop has dimension at most `1`, so countably many loops cover no set of a larger dimension.
* **`C¹` charts preserve the dimension** (`QcEmbedding.dimH_image`): a `C¹` embedding with
  invertible derivative is locally bi-Lipschitz, so whatever its dilatation it does not change the
  Hausdorff dimension of any subset of its domain. The charts of `QuasiInvariance.lean` and
  `Collar.lean` compare moduli and never dimensions; a correspondence between sets of different
  dimension, such as a smooth curve and a fractal, or a Julia set of dimension below `2` and the
  boundary of the Mandelbrot set, is not `C¹`. It is quasi-conformal, and the distortion of the
  dimension is then bounded by the dilatation `K` (Astala, Acta Math. 173, 1994; not formalized): a
  set of dimension `d` goes to a set of dimension at most `2Kd / (2 + (K − 1) d)`, and `K = 1`
  gives `d`.
* **Parametrizations by an interval** (`dimH_le_inv_of_holderOnWith`, `holder_mul_le_one`): an
  `α`-Hölder parametrization of a set of dimension `d` has `α d ≤ 1`. Given Shishikura's theorem
  (`ShishikuraDimension`, a published statement that is a hypothesis here), the boundary of the
  Mandelbrot set is not covered by countably many `C¹` loops
  (`ShishikuraDimension.not_subset_iUnion_range`), is not the `C¹` image of any set of dimension
  below `2` (`ShishikuraDimension.two_le_dimH_of_image`), and a parametrization of it by an interval,
  such as the landing map of the external rays that exists exactly when `M` is locally connected
  (Carathéodory), has Hölder exponent at most `1/2` (`ShishikuraDimension.holder_exponent_le_half`).
  `Mlc/Research/PeanoObject.lean` states this in the category of compact Hausdorff spaces.
* **The fiber of a nest** (`ConnectedNest.dimH_kernel_eq_zero_of_divergent`,
  `ConnectedNest.sum_extWidth_loops_bounded_of_dimH_kernel_pos`): the fiber of the parameter `c`, the
  kernel of its nest, is a point exactly when the local connectivity holds at `c`. If the moduli of
  the annuli add up to infinity, the fiber is the point `c` and has dimension `0`; if it has positive
  dimension, the moduli add up to a finite bound. The loops see a fractal fiber only as a set that
  is not a point.
-/

namespace MLC.Research

open MeasureTheory ENNReal Set Topology Metric NNReal

noncomputable section

/-! ### Smooth curves have dimension at most one -/

/-- The image of a `C¹` loop has Hausdorff dimension at most `1`: it is a Lipschitz image of an
interval. -/
lemma IsLoop.dimH_range_le {γ : ℝ → ℂ} (h : IsLoop γ) : dimH (range γ) ≤ 1 := by
  have := h.1.dimH_range_le
  simpa using this

/-- Countably many `C¹` loops cover no set of Hausdorff dimension larger than `1`. -/
lemma dimH_iUnion_range_le_one {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ}
    (h : ∀ i, IsLoop (γ i)) : dimH (⋃ i, range (γ i)) ≤ 1 :=
  (dimH_iUnion _).trans_le (iSup_le fun i => (h i).dimH_range_le)

/-! ### Dimension under a `C¹` embedding -/

lemma QcEmbedding.dimH_image_le {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ} (h : QcEmbedding Ω φ K)
    {S : Set ℂ} (hS : S ⊆ Ω) : dimH (φ '' S) ≤ dimH S :=
  dimH_image_le_of_locally_lipschitzOn fun x hx => by
    obtain ⟨C, t, ht, hC⟩ :=
      (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds (hS hx))).exists_lipschitzOnWith
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hC⟩

/-- The inverse of a `C¹` embedding with invertible derivative is locally Lipschitz, so the image
of a set has at least its dimension. -/
lemma QcEmbedding.le_dimH_image {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ} (h : QcEmbedding Ω φ K)
    {S : Set ℂ} (hS : S ⊆ Ω) : dimH S ≤ dimH (φ '' S) := by
  classical
  set ψ : ℂ → ℂ := Function.invFunOn φ Ω with hψ
  have hleft : ∀ z ∈ Ω, ψ (φ z) = z := fun z hz => h.injOn.leftInvOn_invFunOn hz
  have himg : ψ '' (φ '' S) = S := (h.injOn.leftInvOn_invFunOn.mono hS).image_image
  calc dimH S = dimH (ψ '' (φ '' S)) := by rw [himg]
    _ ≤ dimH (φ '' S) := by
      refine dimH_image_le_of_locally_lipschitzOn fun y hy => ?_
      obtain ⟨a, haS, rfl⟩ := hy
      have haΩ : a ∈ Ω := hS haS
      let e : ℂ ≃L[ℝ] ℂ :=
        ((fderiv ℝ φ a : ℂ →ₗ[ℝ] ℂ).equivOfDetNeZero (h.det_ne a haΩ)).toContinuousLinearEquiv
      have hs : HasStrictFDerivAt φ (e : ℂ →L[ℝ] ℂ) a := h.hasStrictFDerivAt haΩ
      set g : ℂ → ℂ := hs.localInverse φ e a with hg
      obtain ⟨C, L, hL, hCg⟩ := hs.to_localInverse.exists_lipschitzOnWith
      have h1 : ∀ᶠ w in 𝓝 (φ a), φ (g w) = w := hs.eventually_right_inverse
      have h2 : ∀ᶠ w in 𝓝 (φ a), g w ∈ Ω :=
        hs.localInverse_continuousAt.eventually
          (h.isOpen.mem_nhds (by rw [hs.localInverse_apply_image]; exact haΩ))
      have h3 : φ '' Ω ∈ 𝓝 (φ a) :=
        (h.isOpen_image h.isOpen subset_rfl).mem_nhds ⟨a, haΩ, rfl⟩
      have hmem : ({w | φ (g w) = w ∧ g w ∈ Ω} ∩ L) ∩ φ '' Ω ∈ 𝓝 (φ a) :=
        Filter.inter_mem (Filter.inter_mem (h1.and h2) hL) h3
      refine ⟨C, _, mem_nhdsWithin_of_mem_nhds hmem, ?_⟩
      have key : ∀ v ∈ ({w | φ (g w) = w ∧ g w ∈ Ω} ∩ L) ∩ φ '' Ω, ψ v = g v := by
        rintro v ⟨⟨⟨hv1, hv2⟩, -⟩, z, hz, rfl⟩
        rw [hleft z hz]
        exact (h.injOn hv2 hz hv1).symm
      intro w hw w' hw'
      rw [key w hw, key w' hw']
      exact hCg hw.1.2 hw'.1.2

/-- **A `C¹` embedding preserves the Hausdorff dimension.** A `C¹` embedding with invertible
derivative is locally bi-Lipschitz, so it does not change the dimension of any subset of its
domain. In particular no `C¹` chart, whatever its dilatation, carries a set of dimension `d` to a
set of another dimension: the charts of `QuasiInvariance.lean` and `Collar.lean` cannot create or
destroy a fractal, which is why they compare moduli and not dimensions. -/
theorem QcEmbedding.dimH_image {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ} (h : QcEmbedding Ω φ K)
    {S : Set ℂ} (hS : S ⊆ Ω) : dimH (φ '' S) = dimH S :=
  le_antisymm (h.dimH_image_le hS) (h.le_dimH_image hS)

/-! ### Parametrizations by an interval -/

/-- **A Hölder parametrization raises the dimension by at most the factor `1/α`.** A set covered by
the image of an interval under an `α`-Hölder map has Hausdorff dimension at most `1/α`; for a
Lipschitz map (`α = 1`) at most `1`. -/
theorem dimH_le_inv_of_holderOnWith {T : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {C α : ℝ≥0}
    (hα : 0 < α) (hγ : HolderOnWith C α γ (Icc a b)) (hab : a < b) (hT : T ⊆ γ '' Icc a b) :
    dimH T ≤ 1 / α := by
  have hdim : dimH (Icc a b) = 1 := by
    rw [Real.dimH_of_nonempty_interior (by rw [interior_Icc]; exact nonempty_Ioo.2 hab)]
    simp
  calc dimH T ≤ dimH (γ '' Icc a b) := dimH_mono hT
    _ ≤ dimH (Icc a b) / α := hγ.dimH_image_le hα
    _ = 1 / α := by rw [hdim]

/-- If a set of dimension at least `d` is covered by an `α`-Hölder image of an interval, then
`α d ≤ 1`: the exponent of a parametrization of a fractal is at most the reciprocal of its
dimension. -/
theorem holder_mul_le_one {T : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {C α d : ℝ≥0} (hα : 0 < α)
    (hγ : HolderOnWith C α γ (Icc a b)) (hab : a < b) (hT : T ⊆ γ '' Icc a b)
    (hd : (d : ℝ≥0∞) ≤ dimH T) : α * d ≤ 1 := by
  have h1 : (d : ℝ≥0∞) ≤ 1 / α := hd.trans (dimH_le_inv_of_holderOnWith hα hγ hab hT)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hα.ne')) (Or.inl (by simp))] at h1
  rw [mul_comm]
  exact_mod_cast h1

/-! ### The boundary of the Mandelbrot set -/

/-- **Shishikura (1998).** The boundary of the Mandelbrot set has Hausdorff dimension `2`: it is a
fractal, of topological dimension `1` and Hausdorff dimension `2`. Published; not formalized. -/
def ShishikuraDimension : Prop :=
  dimH (frontier MLC.Quadratic.MandelbrotSet) = 2

namespace ShishikuraDimension

variable (hS : ShishikuraDimension)
include hS

/-- The boundary of the Mandelbrot set is not covered by countably many `C¹` loops. -/
theorem not_subset_iUnion_range {ι : Type*} [Countable ι] {γ : ι → ℝ → ℂ}
    (hγ : ∀ i, IsLoop (γ i)) :
    ¬ frontier MLC.Quadratic.MandelbrotSet ⊆ ⋃ i, range (γ i) := fun hsub => by
  have h1 := (dimH_mono hsub).trans (dimH_iUnion_range_le_one hγ)
  rw [hS] at h1
  norm_num at h1

/-- **The Hölder barrier of the boundary.** A parametrization of the boundary of the Mandelbrot set
by an interval is at best `1/2`-Hölder; in particular it is not Lipschitz. -/
theorem holder_exponent_le_half {γ : ℝ → ℂ} {a b : ℝ} {C α : ℝ≥0} (hα : 0 < α)
    (hγ : HolderOnWith C α γ (Icc a b)) (hab : a < b)
    (hT : frontier MLC.Quadratic.MandelbrotSet ⊆ γ '' Icc a b) : α ≤ 1 / 2 := by
  have h := holder_mul_le_one hα hγ hab hT (d := 2) (by rw [hS]; simp)
  rw [← NNReal.coe_le_coe] at h ⊢
  push_cast at h ⊢
  linarith

/-- **No `C¹` chart carries a lower-dimensional set onto the boundary.** If a `C¹` embedding
carries a set `S` onto a set that contains the boundary of the Mandelbrot set, then `S` has
dimension `2`: the boundary is not the `C¹` image of a smooth curve or of any set of smaller
dimension. -/
theorem two_le_dimH_of_image {Ω : Set ℂ} {φ : ℂ → ℂ} {K : ℝ} (hφ : QcEmbedding Ω φ K)
    {S : Set ℂ} (hSΩ : S ⊆ Ω) (hsub : frontier MLC.Quadratic.MandelbrotSet ⊆ φ '' S) :
    2 ≤ dimH S := by
  rw [← hφ.dimH_image hSΩ, ← hS]
  exact dimH_mono hsub

end ShishikuraDimension

/-! ### The fiber of a nest -/

namespace ConnectedNest

variable {S : Set ℂ} {c : ℂ}

/-- **Divergent moduli leave a point.** If the moduli of the annuli of a nest add up to infinity,
its kernel is the point `c`: the fiber has dimension `0`. -/
theorem kernel_eq_singleton_of_divergent {D : ConnectedNest S c} (h : D.DivergentModuli) :
    D.kernel = {c} := by
  refine Subset.antisymm (fun z hz => ?_) (singleton_subset_iff.2 D.mem_kernel)
  by_contra hzc
  obtain ⟨N, hN⟩ := h.shrinking (dist_pos.2 hzc)
  exact lt_irrefl _ (mem_ball.1 (hN N le_rfl (D.kernel_subset_closure N hz)))

/-- The fiber of a nest whose moduli add up to infinity has Hausdorff dimension `0`. -/
theorem dimH_kernel_eq_zero_of_divergent {D : ConnectedNest S c} (h : D.DivergentModuli) :
    dimH D.kernel = 0 := by
  rw [kernel_eq_singleton_of_divergent h]
  exact dimH_singleton c

/-- **A fractal fiber has a finite total modulus.** If the kernel of a nest has positive Hausdorff
dimension, the moduli of its annuli add up to a finite bound: the loops, which have dimension `1`,
go around a set that is not a point only a bounded number of times, in the sense of moduli. -/
theorem sum_extWidth_loops_bounded_of_dimH_kernel_pos (D : ConnectedNest S c)
    (hpos : 0 < dimH D.kernel) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n, ∑ j ∈ Finset.range n, extWidth volume (D.loops j) ≤ B := by
  obtain ⟨z, hz, hzc⟩ : ∃ z ∈ D.kernel, z ≠ c := by
    by_contra hcon
    push_neg at hcon
    have hsub : D.kernel.Subsingleton := fun x hx y hy => by rw [hcon x hx, hcon y hy]
    rw [dimH_subsingleton hsub] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨R, hR⟩ := (D.compact_closure 0).isBounded.subset_closedBall c
  refine ⟨_, ?_, fun n =>
    D.sum_extWidth_loops_le (dist_pos.2 hzc) hR (D.kernel_subset_closure n hz) le_rfl⟩
  exact ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (pow_ne_zero 2 (ENNReal.ofReal_pos.2 (Real.log_pos one_lt_two)).ne')

end ConnectedNest

end

end MLC.Research
