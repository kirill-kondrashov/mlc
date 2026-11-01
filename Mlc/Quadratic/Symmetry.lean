import Yoccoz.Quadratic.Complex.Basic

/-!
# Elementary symmetries of the quadratic family

Every map `f_c(z) = z² + c` satisfies `f_c(-z) = f_c(z)`, and complex conjugation
commutes with `f_c` when the parameter is conjugated too.  Consequently:

* the filled Julia set `K c` is symmetric under `z ↦ -z`, hence so is `J c = ∂K c`;
* `K (conj c)` is the complex conjugate of `K c`;
* the Mandelbrot set is invariant under complex conjugation.

These are the elementary symmetries used in Milnor's lectures and in the
Douady--Hubbard theory of the Mandelbrot set.
-/

namespace MLC.Quadratic

open ComplexConjugate

noncomputable section

lemma orbit_conj (c z : ℂ) (n : ℕ) :
    orbit (conj c) (conj z) n = conj (orbit c z n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_succ (conj c) (conj z) n, orbit_succ c z n, ih]
    simp [fc]

lemma boundedOrbit_conj_iff (c z : ℂ) :
    boundedOrbit (conj c) (conj z) ↔ boundedOrbit c z := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, fun n => ?_⟩
    have h := hM n
    rw [orbit_conj, Complex.norm_conj] at h
    exact h
  · rintro ⟨M, hM⟩
    refine ⟨M, fun n => ?_⟩
    rw [orbit_conj, Complex.norm_conj]
    exact hM n

/-- The Mandelbrot set is invariant under complex conjugation. -/
theorem mandelbrot_conj_iff (c : ℂ) : conj c ∈ MandelbrotSet ↔ c ∈ MandelbrotSet := by
  show boundedOrbit (conj c) 0 ↔ boundedOrbit c 0
  simpa using boundedOrbit_conj_iff c 0

lemma orbit_neg_succ (c z : ℂ) (n : ℕ) :
    orbit c (-z) (n + 1) = orbit c z (n + 1) := by
  induction n with
  | zero =>
    rw [orbit_succ c (-z) 0, orbit_succ c z 0, orbit_zero, orbit_zero]
    simp only [fc]
    ring
  | succ n ih =>
    rw [orbit_succ c (-z) (n + 1), orbit_succ c z (n + 1), ih]

lemma boundedOrbit_neg_iff (c z : ℂ) : boundedOrbit c (-z) ↔ boundedOrbit c z := by
  have key : ∀ w : ℂ, boundedOrbit c w → boundedOrbit c (-w) := by
    rintro w ⟨M, hM⟩
    refine ⟨max M ‖w‖, fun n => ?_⟩
    cases n with
    | zero =>
      rw [orbit_zero, norm_neg]
      exact le_max_right _ _
    | succ k =>
      rw [orbit_neg_succ]
      exact (hM (k + 1)).trans (le_max_left _ _)
  exact ⟨fun h => by have := key (-z) h; rwa [neg_neg] at this, key z⟩

/-- The filled Julia set is symmetric under `z ↦ -z`. -/
theorem neg_mem_K_iff (c z : ℂ) : -z ∈ K c ↔ z ∈ K c :=
  boundedOrbit_neg_iff c z

/-- The filled Julia set of `conj c` is the complex conjugate of that of `c`. -/
theorem conj_mem_K_iff (c z : ℂ) : conj z ∈ K (conj c) ↔ z ∈ K c :=
  boundedOrbit_conj_iff c z

/-- The Julia set is symmetric under `z ↦ -z`. -/
theorem neg_mem_J_iff (c z : ℂ) : -z ∈ J c ↔ z ∈ J c := by
  show -z ∈ frontier (K c) ↔ z ∈ frontier (K c)
  have himg : (Homeomorph.neg ℂ) '' K c = K c := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      show -u ∈ K c
      exact (neg_mem_K_iff c u).mpr hu
    · intro hw
      exact ⟨-w, (neg_mem_K_iff c w).mpr hw, by simp⟩
  have hfr : (Homeomorph.neg ℂ) '' frontier (K c) = frontier (K c) := by
    rw [Homeomorph.image_frontier, himg]
  constructor
  · intro hz
    have hmem : (Homeomorph.neg ℂ) (-z) ∈ (Homeomorph.neg ℂ) '' frontier (K c) := ⟨-z, hz, rfl⟩
    rw [hfr] at hmem
    simpa using hmem
  · intro hz
    have hmem : (Homeomorph.neg ℂ) z ∈ (Homeomorph.neg ℂ) '' frontier (K c) := ⟨z, hz, rfl⟩
    rw [hfr] at hmem
    simpa using hmem

end

end MLC.Quadratic
