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

/-- The quadratic polynomial $f_c(z) = z^2 + c$.

Details:
This is the fundamental map of the quadratic family. The parameter $c$ defines the specific polynomial.
This map is the simplest non-trivial holomorphic dynamical system. -/
def fc (c : ℂ) : ℂ → ℂ := fun z => z^2 + c

/-- The forward orbit of $z_0$ under $f_c$.

Details:
The orbit is the sequence of points $z_0, z_1, z_2, \dots$ where $z_{n+1} = f_c(z_n)$.
Formally, `orbit c z n` is the $n$-th iterate of $f_c$ applied to $z$. -/
def orbit (c : ℂ) (z0 : ℂ) : ℕ → ℂ := fun n => (Nat.iterate (fc c) n) z0

@[simp] lemma orbit_zero (c z : ℂ) : orbit c z 0 = z := rfl

@[simp] lemma orbit_succ (c z : ℂ) (n : ℕ) :
    orbit c z (n+1) = fc c (orbit c z n) := by
  -- `Function.iterate_succ : iterate f (n+1) = iterate f n ∘ f`
  simpa [orbit, Function.comp] using
    congrArg (fun g => g z) (Function.iterate_succ' (fc c) n)

/-- Boundedness of an orbit.

Details:
An orbit is bounded if there exists a real number $M$ such that $|f_c^n(z)| \le M$ for all $n$.
This property determines whether a point belongs to the filled Julia set. -/
def boundedOrbit (c z : ℂ) : Prop :=
  ∃ M : ℝ, ∀ n, ‖orbit c z n‖ ≤ M

/-- Filled Julia set.

Details:
The filled Julia set $K(c)$ consists of all initial points $z$ whose orbit under $f_c$ remains bounded.
This is a compact subset of the complex plane. -/
def K (c : ℂ) : Set ℂ := { z | boundedOrbit c z }

/-- Julia set as the topological boundary of $K(c)$.

Details:
The Julia set $J(c)$ is the common boundary of the filled Julia set $K(c)$ and its complement (the basin of infinity).
It is the locus of chaotic dynamics. -/
def J (c : ℂ) : Set ℂ := frontier (K c)

/-- The Mandelbrot set.

Details:
The Mandelbrot set $\mathcal{M}$ is the set of parameters $c$ for which the orbit of the critical point $0$ is bounded.
If $c \in \mathcal{M}$, the filled Julia set $K(c)$ is connected. If $c \notin \mathcal{M}$, $K(c)$ is a Cantor set. -/
def MandelbrotSet : Set ℂ := { c | boundedOrbit c 0 }

/-! ## Elementary norm facts -/

@[simp] lemma norm_sq (z : ℂ) : ‖z^2‖ = ‖z‖^2 := by
  -- ‖z^2‖ = ‖z‖ * ‖z‖ and `‖z‖^2` is `(‖z‖)^2`.
  simp [pow_two]

/-- A convenient escape radius depending on $|c|$.

Details:
$R(c) = \max(2, 1 + |c|)$ is chosen large enough so that if $|z| > R(c)$, the orbit of $z$ necessarily escapes to infinity.
See the Escape Lemma for the proof of this property. -/
def R (c : ℂ) : ℝ := max 2 (1 + ‖c‖)

@[simp] lemma R_ge_two (c : ℂ) : R c ≥ 2 := by simp [R]
@[simp] lemma R_ge_one_plus_c (c : ℂ) : R c ≥ 1 + ‖c‖ := by simp [R]

/-- The Mandelbrot set is connected.

Details:
This is a fundamental theorem by Douady and Hubbard. It states that the set of parameters $c$ for which $0$ has a bounded orbit is connected.
Source: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984, Theorem 1, Chapter VIII] <https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf> (p. 47) -/
axiom mandelbrot_set_connected : IsConnected MandelbrotSet

/-- The filled Julia set is connected if $c$ is in the Mandelbrot set.

Details:
If the critical point $0$ has a bounded orbit, then the filled Julia set $K(c)$ is connected.
Otherwise, $K(c)$ is a Cantor set (totally disconnected).
Source: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984, Proposition 1, Chapter VIII] <https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf> (p. 47) -/
axiom filled_julia_set_connected {c : ℂ} (h : c ∈ MandelbrotSet) : IsConnected (K c)

/-! ## Conformal Modulus -/

/-- A topological annulus (doubly connected domain). -/
structure Annulus where
  val : Set ℂ

instance : Coe Annulus (Set ℂ) := ⟨Annulus.val⟩

/-- Property of being a conformal annulus. -/
opaque IsAnnulus (S : Set ℂ) : Prop

/-- A round annulus $ann(a; r, R)$ as an `Annulus`. -/
def RoundAnnulus (a : ℂ) (r R : ℝ) : Annulus :=
  ⟨{ z | r < ‖z - a‖ ∧ ‖z - a‖ < R }⟩ -- open region between circles of radii r and R

opaque modulus (S : Annulus) : ℝ

/-- The modulus of the empty set is 0. -/
axiom modulus_empty : modulus ⟨(∅ : Set ℂ)⟩ = 0

/-- Modulus is non-negative.

Details:
The modulus measures the "thickness" of an annulus, which must be non-negative. -/
axiom modulus_nonneg (S : Annulus) : 0 ≤ modulus S

/-- A sub-annulus A is essential in S if it separates the boundary components of S. -/
opaque EssentialIn (A S : Annulus) : Prop

/-- Axiom: Superadditivity of modulus for disjoint essential annuli (Grötzsch Inequality).

Details:
If $A$ and $B$ are disjoint annuli nested within $S$, then the sum of their moduli is less than or equal to the modulus of $S$.
This inequality is crucial for proving convergence of moduli sums in the Yoccoz puzzle analysis.
Reference: Milnor, Dynamics in One Complex Variable, Corollary B.5 -/
axiom groetzsch_inequality_axiom {A B S : Annulus}
  (h_disj : Disjoint (A : Set ℂ) B) (h_sub : (A : Set ℂ) ∪ B ⊆ S)
  (h_ess_A : EssentialIn A S) (h_ess_B : EssentialIn B S)
  (h_ann_A : IsAnnulus A) (h_ann_B : IsAnnulus B) (h_ann_S : IsAnnulus S) :
  modulus A + modulus B ≤ modulus S

/-- Axiom: Monotonicity of modulus.
    If U ⊆ V, then modulus(U) ≤ modulus(V). -/
axiom modulus_mono_axiom {U V : Set ℂ} (h : U ⊆ V) : modulus ⟨U⟩ ≤ modulus ⟨V⟩

end

end Quadratic
end MLC
