import Mlc.CertifiedTrappingRegions

/-!
# Finite unions of rational trapping rectangles

Soundness requires only finite data, critical-point containment, forward
invariance, and a certified bound.  Positive coordinate margins additionally
certify strict trapping.  The explicit period-two example uses two rectangles
around `0` and `-1`.  Density of a family is a separate hypothesis.
-/

namespace MLC
namespace FiniteTrapping

open Set
open CertifiedTrapping (RationalBox)

noncomputable section

/-- A finite union represented by an actual list of nondegenerate rational boxes. -/
def boxUnion (boxes : List RationalBox) : Set ℂ :=
  {z | ∃ B ∈ boxes, z ∈ B.toSet}

/-- The closed inset of a rectangle at coordinate distance at least `δ`
from each of its four sides. -/
def marginSet (B : RationalBox) (δ : ℝ) : Set ℂ :=
  {z | (B.reLo : ℝ) + δ ≤ z.re ∧ z.re ≤ (B.reHi : ℝ) - δ ∧
    (B.imLo : ℝ) + δ ≤ z.im ∧ z.im ≤ (B.imHi : ℝ) - δ}

theorem marginSet_subset (B : RationalBox) {δ : ℝ} (hδ : 0 ≤ δ) :
    marginSet B δ ⊆ B.toSet := by
  intro z hz
  rcases hz with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem marginSet_subset_interior (B : RationalBox) {δ : ℝ} (hδ : 0 < δ) :
    marginSet B δ ⊆ interior B.toSet := by
  let U : Set ℂ := {z | (B.reLo : ℝ) < z.re ∧ z.re < (B.reHi : ℝ) ∧
    (B.imLo : ℝ) < z.im ∧ z.im < (B.imHi : ℝ)}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hsub : U ⊆ B.toSet :=
    fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  intro z hz
  apply (interior_maximal hsub hopen)
  rcases hz with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Perturbing an inset point by at most its margin stays in the closed box. -/
theorem mem_box_of_dist_le_margin (B : RationalBox) {δ : ℝ} {z w : ℂ}
    (hz : z ∈ marginSet B δ) (hw : dist w z ≤ δ) : w ∈ B.toSet := by
  rw [dist_eq_norm] at hw
  have hre := abs_le.mp ((Complex.abs_re_le_norm (w - z)).trans hw)
  have him := abs_le.mp ((Complex.abs_im_le_norm (w - z)).trans hw)
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rcases hz with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨by linarith [hre.1], by linarith [hre.2],
    by linarith [him.1], by linarith [him.2]⟩

/-- A finite-union trapping certificate, without any density assumption. -/
structure TrappingCertificate where
  parameterBox : RationalBox
  trapBoxes : List RationalBox
  zero_mem_trap : (0 : ℂ) ∈ boxUnion trapBoxes
  forward_invariant :
    ∀ c ∈ parameterBox.toSet, ∀ z ∈ boxUnion trapBoxes,
      Quadratic.fc c z ∈ boxUnion trapBoxes
  bound : ℝ
  trap_bounded : ∀ z ∈ boxUnion trapBoxes, ‖z‖ ≤ bound

namespace TrappingCertificate

def trapSet (C : TrappingCertificate) : Set ℂ := boxUnion C.trapBoxes

/-- A uniform margin puts every image in the inset of some listed rectangle. -/
def HasMargin (C : TrappingCertificate) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ c ∈ C.parameterBox.toSet, ∀ z ∈ C.trapSet,
    ∃ B ∈ C.trapBoxes, Quadratic.fc c z ∈ marginSet B δ

theorem forward_mem_rectangle_interior (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) {c z : ℂ}
    (hc : c ∈ C.parameterBox.toSet) (hz : z ∈ C.trapSet) :
    ∃ B ∈ C.trapBoxes, Quadratic.fc c z ∈ interior B.toSet := by
  obtain ⟨B, hB, hm⟩ := h.2 c hc z hz
  exact ⟨B, hB, marginSet_subset_interior B h.1 hm⟩

theorem forward_mem_interior (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) {c z : ℂ}
    (hc : c ∈ C.parameterBox.toSet) (hz : z ∈ C.trapSet) :
    Quadratic.fc c z ∈ interior C.trapSet := by
  obtain ⟨B, hB, hm⟩ := C.forward_mem_rectangle_interior h hc hz
  exact interior_mono (fun w hw => (show w ∈ C.trapSet from ⟨B, hB, hw⟩)) hm

theorem orbit_mem_trap (C : TrappingCertificate) {c : ℂ}
    (hc : c ∈ C.parameterBox.toSet) :
    ∀ n, Quadratic.orbit c 0 n ∈ C.trapSet := by
  intro n
  induction n with
  | zero => exact C.zero_mem_trap
  | succ n ih =>
      rw [Quadratic.orbit_succ]
      exact C.forward_invariant c hc _ ih

theorem parameter_mem_mandelbrot (C : TrappingCertificate) {c : ℂ}
    (hc : c ∈ C.parameterBox.toSet) : c ∈ Quadratic.MandelbrotSet := by
  change Quadratic.boundedOrbit c 0
  exact ⟨C.bound, fun n => C.trap_bounded _ (C.orbit_mem_trap hc n)⟩

theorem parameterBox_subset_mandelbrot (C : TrappingCertificate) :
    C.parameterBox.toSet ⊆ Quadratic.MandelbrotSet :=
  fun _ hc => C.parameter_mem_mandelbrot hc

/-- The same closed trapping region survives parameter perturbations up to the margin. -/
theorem forward_invariant_of_parameter_dist_le (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) {c c' : ℂ} (hc : c ∈ C.parameterBox.toSet)
    (hc' : dist c' c ≤ δ) {z : ℂ} (hz : z ∈ C.trapSet) :
    Quadratic.fc c' z ∈ C.trapSet := by
  obtain ⟨B, hB, hm⟩ := h.2 c hc z hz
  refine ⟨B, hB, mem_box_of_dist_le_margin B hm ?_⟩
  simpa only [dist_eq_norm, Quadratic.fc, add_sub_add_left_eq_sub] using hc'

theorem orbit_mem_trap_of_parameter_dist_le (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) {c c' : ℂ} (hc : c ∈ C.parameterBox.toSet)
    (hc' : dist c' c ≤ δ) : ∀ n, Quadratic.orbit c' 0 n ∈ C.trapSet := by
  intro n
  induction n with
  | zero => exact C.zero_mem_trap
  | succ n ih =>
      rw [Quadratic.orbit_succ]
      exact C.forward_invariant_of_parameter_dist_le h hc hc' ih

/-- Robust membership does not require the perturbed parameter to remain in its box. -/
theorem parameter_mem_mandelbrot_of_dist_le (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) {c c' : ℂ} (hc : c ∈ C.parameterBox.toSet)
    (hc' : dist c' c ≤ δ) : c' ∈ Quadratic.MandelbrotSet := by
  change Quadratic.boundedOrbit c' 0
  exact ⟨C.bound,
    fun n => C.trap_bounded _ (C.orbit_mem_trap_of_parameter_dist_le h hc hc' n)⟩

theorem ball_subset_mandelbrot (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) {c : ℂ} (hc : c ∈ C.parameterBox.toSet) :
    Metric.ball c δ ⊆ Quadratic.MandelbrotSet :=
  fun _ hc' => C.parameter_mem_mandelbrot_of_dist_le h hc (Metric.mem_ball.mp hc').le

/-- A positive uniform trapping margin certifies interior parameter membership,
including every boundary point of the parameter rectangle. -/
theorem parameterBox_subset_interior_mandelbrot (C : TrappingCertificate) {δ : ℝ}
    (h : C.HasMargin δ) : C.parameterBox.toSet ⊆ interior Quadratic.MandelbrotSet := by
  intro c hc
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  exact ⟨δ, h.1, C.ball_subset_mandelbrot h hc⟩

end TrappingCertificate

/-- Finite increasing stages of finite-union certificates. -/
structure Family where
  stage : ℕ → Finset TrappingCertificate
  monotone : ∀ {n m}, n ≤ m → stage n ⊆ stage m

def Family.innerSet (F : Family) (n : ℕ) : Set ℂ :=
  ⋃ C ∈ F.stage n, C.parameterBox.toSet

theorem Family.innerSet_subset_mandelbrot (F : Family) (n : ℕ) :
    F.innerSet n ⊆ Quadratic.MandelbrotSet := by
  intro c hc
  obtain ⟨C, hc⟩ := mem_iUnion.mp hc
  obtain ⟨_, hc⟩ := mem_iUnion.mp hc
  exact C.parameter_mem_mandelbrot hc

theorem Family.innerSet_mono (F : Family) {n m : ℕ} (h : n ≤ m) :
    F.innerSet n ⊆ F.innerSet m := by
  intro c hc
  obtain ⟨C, hc⟩ := mem_iUnion.mp hc
  obtain ⟨hC, hc⟩ := mem_iUnion.mp hc
  exact mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨F.monotone h hC, hc⟩⟩

/-- Density is a proposition to be proved for a chosen family, not an axiom. -/
def InnerDensity (F : Family) : Prop :=
  ∀ c ∈ Quadratic.MandelbrotSet, ∀ ε > (0 : ℝ),
    ∃ n, ∃ x ∈ F.innerSet n, dist x c < ε

theorem innerSet_closure_eq_mandelbrot (F : Family) (h : InnerDensity F) :
    closure (⋃ n, F.innerSet n) = Quadratic.MandelbrotSet := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro c hc
      obtain ⟨n, hn⟩ := mem_iUnion.mp hc
      exact F.innerSet_subset_mandelbrot n hn
    · exact Molecule.isClosed_mandelbrot
  · intro c hc
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, x, hx, hxc⟩ := h c hc ε hε
    exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, by simpa [dist_comm] using hxc⟩

/-- The parameter square centered at `-1`, with halfwidth `1/256`. -/
def periodTwoParameterBox : RationalBox where
  reLo := -1 - 1 / 256
  reHi := -1 + 1 / 256
  imLo := -1 / 256
  imHi := 1 / 256
  re_lt := by norm_num
  im_lt := by norm_num

/-- The first dynamical square, centered at `0`, with halfwidth `1/16`. -/
def periodTwoZeroBox : RationalBox where
  reLo := -1 / 16
  reHi := 1 / 16
  imLo := -1 / 16
  imHi := 1 / 16
  re_lt := by norm_num
  im_lt := by norm_num

/-- The second dynamical square, centered at `-1`, with halfwidth `1/64`. -/
def periodTwoMinusOneBox : RationalBox where
  reLo := -1 - 1 / 64
  reHi := -1 + 1 / 64
  imLo := -1 / 64
  imHi := 1 / 64
  re_lt := by norm_num
  im_lt := by norm_num

private theorem coordinate_bounds {x y a : ℝ} (ha : 0 ≤ a)
    (hx : -a ≤ x ∧ x ≤ a) (hy : -a ≤ y ∧ y ≤ a) :
    x ^ 2 ≤ a ^ 2 ∧ y ^ 2 ≤ a ^ 2 ∧ -(a * a) ≤ x * y ∧ x * y ≤ a * a := by
  have hax : |x| ≤ a := abs_le.mpr hx
  have hay : |y| ≤ a := abs_le.mpr hy
  have hxy : |x * y| ≤ a * a := by
    rw [abs_mul]
    exact mul_le_mul hax hay (abs_nonneg y) ha
  exact ⟨sq_le_sq.mpr (by simpa [abs_of_nonneg ha] using hax),
    sq_le_sq.mpr (by simpa [abs_of_nonneg ha] using hay), abs_le.mp hxy⟩

/-- The first square maps into the second with a uniform positive margin. -/
theorem periodTwo_zero_to_minusOne {c z : ℂ}
    (hc : c ∈ periodTwoParameterBox.toSet) (hz : z ∈ periodTwoZeroBox.toSet) :
    Quadratic.fc c z ∈ marginSet periodTwoMinusOneBox (1 / 1024) := by
  norm_num [RationalBox.toSet, periodTwoParameterBox] at hc
  norm_num [RationalBox.toSet, periodTwoZeroBox] at hz
  obtain ⟨hr, hi, hp₁, hp₂⟩ :=
    coordinate_bounds (a := (1 / 16 : ℝ)) (by norm_num)
      ⟨hz.1, hz.2.1⟩ ⟨hz.2.2.1, hz.2.2.2⟩
  norm_num [marginSet, periodTwoMinusOneBox, Quadratic.fc, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  rcases hc with ⟨hc₁, hc₂, hc₃, hc₄⟩
  exact ⟨by nlinarith [sq_nonneg z.re], by nlinarith [sq_nonneg z.im],
    by nlinarith, by nlinarith⟩

/-- The second square maps back into the first with the same margin. -/
theorem periodTwo_minusOne_to_zero {c z : ℂ}
    (hc : c ∈ periodTwoParameterBox.toSet) (hz : z ∈ periodTwoMinusOneBox.toSet) :
    Quadratic.fc c z ∈ marginSet periodTwoZeroBox (1 / 1024) := by
  norm_num [RationalBox.toSet, periodTwoParameterBox] at hc
  norm_num [RationalBox.toSet, periodTwoMinusOneBox] at hz
  obtain ⟨hr, hi, hp₁, hp₂⟩ :=
    coordinate_bounds (x := z.re + 1) (y := z.im) (a := (1 / 64 : ℝ))
      (by norm_num) ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
      ⟨hz.2.2.1, hz.2.2.2⟩
  norm_num [marginSet, periodTwoZeroBox, Quadratic.fc, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  rcases hc with ⟨hc₁, hc₂, hc₃, hc₄⟩
  rcases hz with ⟨hz₁, hz₂, hz₃, hz₄⟩
  exact ⟨by nlinarith [sq_nonneg (z.re + 1)], by nlinarith [sq_nonneg z.im],
    by nlinarith, by nlinarith⟩

theorem periodTwo_forward_margin {c z : ℂ}
    (hc : c ∈ periodTwoParameterBox.toSet)
    (hz : z ∈ boxUnion [periodTwoZeroBox, periodTwoMinusOneBox]) :
    ∃ B ∈ [periodTwoZeroBox, periodTwoMinusOneBox],
      Quadratic.fc c z ∈ marginSet B (1 / 1024) := by
  obtain ⟨B, hB, hz⟩ := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl
  · exact ⟨periodTwoMinusOneBox, by simp, periodTwo_zero_to_minusOne hc hz⟩
  · exact ⟨periodTwoZeroBox, by simp, periodTwo_minusOne_to_zero hc hz⟩

theorem periodTwo_trap_bounded {z : ℂ}
    (hz : z ∈ boxUnion [periodTwoZeroBox, periodTwoMinusOneBox]) : ‖z‖ ≤ 2 := by
  obtain ⟨B, hB, hz⟩ := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  have hre : |z.re| ≤ (65 / 64 : ℝ) := by
    rcases hB with rfl | rfl
    · norm_num [RationalBox.toSet, periodTwoZeroBox] at hz
      exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
    · norm_num [RationalBox.toSet, periodTwoMinusOneBox] at hz
      exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
  have him : |z.im| ≤ (1 / 16 : ℝ) := by
    rcases hB with rfl | rfl
    · norm_num [RationalBox.toSet, periodTwoZeroBox] at hz
      exact abs_le.mpr ⟨hz.2.2.1, hz.2.2.2⟩
    · norm_num [RationalBox.toSet, periodTwoMinusOneBox] at hz
      exact abs_le.mpr ⟨by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

/-- An explicit two-rectangle certificate around the period-two parameter `-1`. -/
def periodTwoCertificate : TrappingCertificate where
  parameterBox := periodTwoParameterBox
  trapBoxes := [periodTwoZeroBox, periodTwoMinusOneBox]
  zero_mem_trap := ⟨periodTwoZeroBox, by simp,
    by norm_num [RationalBox.toSet, periodTwoZeroBox]⟩
  forward_invariant := by
    intro c hc z hz
    obtain ⟨B, hB, hm⟩ := periodTwo_forward_margin hc hz
    exact ⟨B, hB, marginSet_subset B (by norm_num) hm⟩
  bound := 2
  trap_bounded := fun _ hz => periodTwo_trap_bounded hz

theorem periodTwoCertificate_hasMargin :
    periodTwoCertificate.HasMargin (1 / 1024) :=
  ⟨by norm_num, fun _ hc _ hz => periodTwo_forward_margin hc hz⟩

theorem minus_one_mem_periodTwoParameterBox :
    (-1 : ℂ) ∈ periodTwoParameterBox.toSet := by
  norm_num [RationalBox.toSet, periodTwoParameterBox]

theorem periodTwoParameterBox_subset_mandelbrot :
    periodTwoParameterBox.toSet ⊆ Quadratic.MandelbrotSet :=
  periodTwoCertificate.parameterBox_subset_mandelbrot

theorem periodTwoParameterBox_subset_interior_mandelbrot :
    periodTwoParameterBox.toSet ⊆ interior Quadratic.MandelbrotSet :=
  periodTwoCertificate.parameterBox_subset_interior_mandelbrot
    periodTwoCertificate_hasMargin

end
end FiniteTrapping
end MLC
