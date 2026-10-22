import Mlc.CertifiedTrappingRegions

/-!
# Obstruction to density of single-rectangle trapping certificates

A nondegenerate, axis-aligned rectangle containing zero can be invariant under
`z ↦ z² + c` only when `|c.re| ≤ 1/2`. Consequently the inner stages defined in
`CertifiedTrappingRegions` cannot be dense in the Mandelbrot set: they cannot
approach the Mandelbrot parameter `-1`.

This obstruction concerns the single-rectangle certificate definition, not
trapping regions that are finite unions of rectangles.
-/

namespace MLC.CertifiedTrapping

open Set

noncomputable section

/-- The closed vertical strip forced by a single rectangular trapping region. -/
def verticalStrip : Set ℂ :=
  {c | -(1 / 2 : ℝ) ≤ c.re ∧ c.re ≤ (1 / 2 : ℝ)}

theorem isClosed_verticalStrip : IsClosed verticalStrip :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

namespace TrappingCertificate

/-- Positive imaginary width and forward invariance force these real bounds. -/
theorem parameter_re_bounds (C : TrappingCertificate) {c : ℂ}
    (hc : c ∈ C.parameterBox.toSet) :
    -(1 / 2 : ℝ) ≤ c.re ∧ c.re ≤ (1 / 2 : ℝ) := by
  have hcU : c ∈ C.trapBox.toSet := by
    simpa [MLC.Quadratic.fc] using
      C.forward_invariant c hc 0 C.zero_mem_trap
  have hwidth : (C.trapBox.imLo : ℝ) < C.trapBox.imHi := by
    exact_mod_cast C.trapBox.im_lt
  have hlo_mem : (⟨c.re, (C.trapBox.imLo : ℝ)⟩ : ℂ) ∈ C.trapBox.toSet :=
    ⟨hcU.1, hcU.2.1, le_rfl, hwidth.le⟩
  have hhi_mem : (⟨c.re, (C.trapBox.imHi : ℝ)⟩ : ℂ) ∈ C.trapBox.toSet :=
    ⟨hcU.1, hcU.2.1, hwidth.le, le_rfl⟩
  have hlo := (C.forward_invariant c hc _ hlo_mem).2.2
  have hhi := (C.forward_invariant c hc _ hhi_mem).2.2
  simp only [MLC.Quadratic.fc, pow_two, Complex.add_im, Complex.mul_im] at hlo hhi
  have hdiff : 0 < (C.trapBox.imHi : ℝ) - C.trapBox.imLo := sub_pos.mpr hwidth
  constructor
  · apply (mul_le_mul_iff_left₀ hdiff).mp
    nlinarith [hlo.2, hhi.1]
  · apply (mul_le_mul_iff_left₀ hdiff).mp
    nlinarith [hlo.1, hhi.2]

theorem parameter_abs_re_le_half (C : TrappingCertificate) {c : ℂ}
    (hc : c ∈ C.parameterBox.toSet) :
    |c.re| ≤ (1 / 2 : ℝ) :=
  abs_le.mpr (C.parameter_re_bounds hc)

theorem parameterBox_subset_verticalStrip (C : TrappingCertificate) :
    C.parameterBox.toSet ⊆ verticalStrip :=
  fun _ hc => C.parameter_re_bounds hc

theorem parameterBox_closure_subset_verticalStrip (C : TrappingCertificate) :
    closure C.parameterBox.toSet ⊆ verticalStrip :=
  closure_minimal C.parameterBox_subset_verticalStrip isClosed_verticalStrip

end TrappingCertificate

namespace Family

theorem innerSet_subset_verticalStrip (F : Family) (n : ℕ) :
    F.innerSet n ⊆ verticalStrip := by
  intro c hc
  rcases mem_iUnion.mp hc with ⟨C, hc⟩
  rcases mem_iUnion.mp hc with ⟨_, hc⟩
  exact C.parameter_re_bounds hc

theorem innerSet_closure_subset_verticalStrip (F : Family) (n : ℕ) :
    closure (F.innerSet n) ⊆ verticalStrip :=
  closure_minimal (F.innerSet_subset_verticalStrip n) isClosed_verticalStrip

theorem innerUnion_subset_verticalStrip (F : Family) :
    (⋃ n, F.innerSet n) ⊆ verticalStrip := by
  intro c hc
  rcases mem_iUnion.mp hc with ⟨n, hc⟩
  exact F.innerSet_subset_verticalStrip n hc

theorem innerUnion_closure_subset_verticalStrip (F : Family) :
    closure (⋃ n, F.innerSet n) ⊆ verticalStrip :=
  closure_minimal F.innerUnion_subset_verticalStrip isClosed_verticalStrip

end Family

/-- The critical orbit at `-1` stays in the invariant pair `{0, -1}`. -/
theorem neg_one_mem_mandelbrot : (-1 : ℂ) ∈ MLC.Quadratic.MandelbrotSet := by
  have horbit : ∀ n, MLC.Quadratic.orbit (-1) 0 n = 0 ∨
      MLC.Quadratic.orbit (-1) 0 n = -1 := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
        rw [MLC.Quadratic.orbit_succ]
        rcases ih with h | h
        · right
          simp [h, MLC.Quadratic.fc]
        · left
          simp [h, MLC.Quadratic.fc]
  change MLC.Quadratic.boundedOrbit (-1) 0
  refine ⟨1, ?_⟩
  intro n
  rcases horbit n with h | h <;> simp [h]

/-- No family of the current single-rectangle certificates has inner density. -/
theorem not_innerDensity (F : Family) : ¬ InnerDensity F := by
  intro h
  obtain ⟨n, x, hx, hdist⟩ :=
    h (-1) neg_one_mem_mandelbrot (1 / 4) (by norm_num)
  have hre := (F.innerSet_subset_verticalStrip n hx).1
  have hsep : (1 / 2 : ℝ) ≤ dist x (-1 : ℂ) := by
    rw [dist_eq_norm]
    calc
      (1 / 2 : ℝ) ≤ (x - (-1 : ℂ)).re := by
        simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
        linarith
      _ ≤ |(x - (-1 : ℂ)).re| := le_abs_self _
      _ ≤ ‖x - (-1 : ℂ)‖ := Complex.abs_re_le_norm _
  linarith

end

end MLC.CertifiedTrapping
