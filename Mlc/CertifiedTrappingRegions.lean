import Mlc.CategoricalMandelbrot

/-!
# Certified finite inner regions

This module formalizes the sound part of the inner-approximation program.
A trapping certificate is finite data together with a forward-invariance
proof.  Its parameter box is contained in the Mandelbrot set.  No density
claim for the resulting inner stages is made here.
-/

namespace MLC
namespace CertifiedTrapping

open Set

noncomputable section

/-- A rational rectangle in the parameter plane or dynamical plane. -/
structure RationalBox where
  reLo : ℚ
  reHi : ℚ
  imLo : ℚ
  imHi : ℚ
  re_lt : reLo < reHi
  im_lt : imLo < imHi

/-- The closed complex rectangle represented by a rational box. -/
def RationalBox.toSet (B : RationalBox) : Set ℂ :=
  {z | (B.reLo : ℝ) ≤ z.re ∧ z.re ≤ B.reHi ∧
    (B.imLo : ℝ) ≤ z.im ∧ z.im ≤ B.imHi}

lemma RationalBox.zero_mem (B : RationalBox) (h : (0 : ℂ) ∈ B.toSet) :
    (0 : ℂ) ∈ B.toSet :=
  h

/-- A finite certificate that a parameter box has a forward-invariant
    trapping region for the critical orbit. -/
structure TrappingCertificate where
  parameterBox : RationalBox
  trapBox : RationalBox
  zero_mem_trap : (0 : ℂ) ∈ trapBox.toSet
  forward_invariant :
    ∀ c ∈ parameterBox.toSet, ∀ z ∈ trapBox.toSet,
      MLC.Quadratic.fc c z ∈ trapBox.toSet
  bound : ℝ
  trap_bounded : ∀ z ∈ trapBox.toSet, ‖z‖ ≤ bound

namespace TrappingCertificate

theorem orbit_mem_trap (C : TrappingCertificate) {c : ℂ}
    (hc : c ∈ C.parameterBox.toSet) :
    ∀ n, MLC.Quadratic.orbit c 0 n ∈ C.trapBox.toSet := by
  intro n
  induction n with
  | zero =>
      exact C.zero_mem_trap
  | succ n ih =>
      rw [MLC.Quadratic.orbit_succ]
      exact C.forward_invariant c hc _ ih

theorem parameter_mem_mandelbrot (C : TrappingCertificate) {c : ℂ}
    (hc : c ∈ C.parameterBox.toSet) :
    c ∈ MLC.Quadratic.MandelbrotSet := by
  change MLC.Quadratic.boundedOrbit c 0
  refine ⟨C.bound, ?_⟩
  intro n
  exact C.trap_bounded _ (C.orbit_mem_trap hc n)

theorem parameterBox_subset_mandelbrot (C : TrappingCertificate) :
    C.parameterBox.toSet ⊆ MLC.Quadratic.MandelbrotSet :=
  fun _ hc => C.parameter_mem_mandelbrot hc

end TrappingCertificate

/-- A finite increasing family of certified inner parameter boxes. -/
structure Family where
  stage : ℕ → Finset TrappingCertificate
  monotone :
    ∀ {n m}, n ≤ m → stage n ⊆ stage m

def Family.innerSet (F : Family) (n : ℕ) : Set ℂ :=
  ⋃ C ∈ F.stage n, C.parameterBox.toSet

theorem Family.innerSet_subset_mandelbrot (F : Family) (n : ℕ) :
    F.innerSet n ⊆ MLC.Quadratic.MandelbrotSet := by
  intro c hc
  rcases mem_iUnion.mp hc with ⟨C, hc⟩
  rcases mem_iUnion.mp hc with ⟨hC, hc⟩
  exact TrappingCertificate.parameter_mem_mandelbrot C hc

theorem Family.innerSet_mono (F : Family) {n m : ℕ} (h : n ≤ m) :
    F.innerSet n ⊆ F.innerSet m := by
  intro c hc
  rcases mem_iUnion.mp hc with ⟨C, hc⟩
  rcases mem_iUnion.mp hc with ⟨hC, hc⟩
  exact mem_iUnion.mpr ⟨C, mem_iUnion.mpr ⟨F.monotone h hC, hc⟩⟩

/-- The missing inner-density assertion is a proposition, not an axiom. -/
def InnerDensity (F : Family) : Prop :=
  ∀ c ∈ MLC.Quadratic.MandelbrotSet, ∀ ε > (0 : ℝ),
    ∃ n, ∃ x ∈ F.innerSet n, dist x c < ε

theorem innerSet_closure_eq_mandelbrot (F : Family) (h : InnerDensity F) :
    closure (⋃ n, F.innerSet n) = MLC.Quadratic.MandelbrotSet := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro c hc
      rcases mem_iUnion.mp hc with ⟨n, hcn⟩
      exact F.innerSet_subset_mandelbrot n hcn
    · exact Molecule.isClosed_mandelbrot
  · intro c hc
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, x, hx, hxc⟩ := h c hc ε hε
    refine ⟨x, ?_, ?_⟩
    · exact mem_iUnion.mpr ⟨n, hx⟩
    · simpa [dist_comm] using hxc

end
end CertifiedTrapping
end MLC
