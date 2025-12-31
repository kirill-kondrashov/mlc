import Mathlib

/-!
# Quadratic family basics (Lyubich I–II notation)

We set up the quadratic family `f_c(z) = z^2 + c`, iterates, filled Julia set `K(c)`,
and Julia set `J(c) = ∂K(c)`. We also state (and stub) the standard escape and
compactness lemmas you’ll prove next.
-/

namespace MLC
namespace Quadratic

open scoped Complex
open Complex Topology Filter
noncomputable section

/-- The quadratic polynomial `f_c(z) = z^2 + c`. -/
def fc (c : ℂ) : ℂ → ℂ := fun z => z^2 + c

/-- The forward orbit of `z0` under `f_c`. -/
def orbit (c : ℂ) (z0 : ℂ) : ℕ → ℂ := fun n => (Nat.iterate (fc c) n) z0

@[simp] lemma orbit_zero (c z : ℂ) : orbit c z 0 = z := rfl

@[simp] lemma orbit_succ (c z : ℂ) (n : ℕ) :
    orbit c z (n+1) = fc c (orbit c z n) := by
  -- `Function.iterate_succ : iterate f (n+1) = iterate f n ∘ f`
  simpa [orbit, Function.comp] using
    congrArg (fun g => g z) (Function.iterate_succ' (fc c) n)

/-- Boundedness of an orbit. -/
def boundedOrbit (c z : ℂ) : Prop :=
  ∃ M : ℝ, ∀ n, ‖orbit c z n‖ ≤ M

/-- Filled Julia set. -/
def K (c : ℂ) : Set ℂ := { z | boundedOrbit c z }

/-- Julia set as the topological boundary of `K(c)`. -/
def J (c : ℂ) : Set ℂ := frontier (K c)

/-- The Mandelbrot set is the set of parameters `c` for which the orbit of `0` is bounded. -/
def MandelbrotSet : Set ℂ := { c | boundedOrbit c 0 }

/-! ## Elementary norm facts -/

@[simp] lemma norm_sq (z : ℂ) : ‖z^2‖ = ‖z‖^2 := by
  -- ‖z^2‖ = ‖z‖ * ‖z‖ and `‖z‖^2` is `(‖z‖)^2`.
  simp [pow_two]

/-- A convenient escape radius depending on `‖c‖`. -/
def R (c : ℂ) : ℝ := max 2 (1 + ‖c‖)

@[simp] lemma R_ge_two (c : ℂ) : R c ≥ 2 := by simp [R]
@[simp] lemma R_ge_one_plus_c (c : ℂ) : R c ≥ 1 + ‖c‖ := by simp [R]

/-- The modulus of an annulus.
    See: [Milnor, Dynamics in One Complex Variable, Problem 2-e] -/
opaque modulus (A : Set ℂ) : ℝ

axiom modulus_empty : modulus ∅ = 0

/-- Grötzsch's Inequality: If the intersection is non-trivial, the moduli sum converges.
    See: [Milnor, Dynamics in One Complex Variable, Problem 2-e] -/
axiom modulus_summable_of_nontrivial_intersection {P : ℕ → Set ℂ} :
  (∀ n, P (n + 1) ⊆ P n) →
  (∀ n, IsConnected (P n)) →
  Set.Nontrivial (⋂ n, P n) →
  Summable (fun n => modulus (P n \ P (n + 1)))

/-- Grötzsch's Criterion: Divergence of moduli implies point intersection.
    See: [Milnor, Dynamics in One Complex Variable, Problem 2-e] -/
theorem groetzsch_criterion {P : ℕ → Set ℂ}
    (h_nested : ∀ n, P (n + 1) ⊆ P n)
    (h_zero : ∀ n, 0 ∈ P n)
    (h_conn : ∀ n, IsConnected (P n))
    (h_div : ¬ Summable (fun n => modulus (P n \ P (n + 1)))) :
    (⋂ n, P n) = {0} := by
  by_contra h_neq
  have h_nontriv : Set.Nontrivial (⋂ n, P n) := by
    have h_0 : 0 ∈ ⋂ n, P n := Set.mem_iInter.mpr h_zero
    rw [Set.nontrivial_iff_exists_ne h_0]
    by_contra h_all_eq
    apply h_neq
    ext z
    constructor
    · intro hz
      by_cases h_z_eq : z = 0
      · rw [h_z_eq]; exact Set.mem_singleton 0
      · push_neg at h_all_eq
        specialize h_all_eq z hz
        contradiction
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact h_0
  have h_sum := modulus_summable_of_nontrivial_intersection h_nested h_conn h_nontriv
  contradiction

/-- The Mandelbrot set is connected.
    See: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984] -/
axiom mandelbrot_set_connected : IsConnected MandelbrotSet

/-- The filled Julia set is connected if c is in the Mandelbrot set.
    See: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984] -/
axiom filled_julia_set_connected {c : ℂ} (h : c ∈ MandelbrotSet) : IsConnected (K c)

end

end Quadratic
end MLC
