import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMDefs
import Mathlib.Topology.Connected.Basic

namespace MLC.Quadratic

open Complex Topology Set

/-!
# Axioms for MLC proof

This file collects the deep theorems used as axioms in this formalization.
These include fundamental results about the connectivity of the Mandelbrot set
and Julia sets (Douady-Hubbard), and the holomorphic motion principle (Slodkowski).
-/

/-- The Mandelbrot set is connected.
    
    Details:
    This is a fundamental theorem by Douady and Hubbard. It states that the set of parameters `c` for which `0` has a bounded orbit is connected.
    Source: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984, Theorem 1, Chapter VIII] <https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf> (p. 47) -/
axiom mandelbrot_set_connected : IsConnected MandelbrotSet

/-- The filled Julia set is connected if `c` is in the Mandelbrot set.

    Details:
    If the critical point `0` has a bounded orbit, then the filled Julia set `K(c)` is connected.
    Otherwise, `K(c)` is a Cantor set (totally disconnected).
    Source: [Douady and Hubbard, Etude dynamique des polynômes complexes, 1984, Proposition 1, Chapter VIII] <https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf> (p. 47) -/
axiom filled_julia_set_connected {c : ℂ} (h : c ∈ MandelbrotSet) : IsConnected (K c)

/-- A holomorphic motion of a set E over the unit disk D. -/
structure HolomorphicMotion (E : Set ℂ) where
  /-- The motion map t ↦ z ↦ f(t, z) -/
  f : ℂ → ℂ → ℂ
  /-- At time 0, it is the identity -/
  h_zero : ∀ z ∈ E, f 0 z = z
  /-- For each fixed time in the unit disk, it is injective on E -/
  h_inj : ∀ t ∈ Metric.ball 0 1, Set.InjOn (f t) E
  /-- For each fixed z in E, it is holomorphic in time on the unit disk -/
  h_holo : ∀ z ∈ E, DifferentiableOn ℂ (fun t ↦ f t z) (Metric.ball 0 1)

/-- Seam axiom: strict monotonicity of the Green function along a fixed unit ray
inside the basin. This is the basin-level radial monotonicity payload used by
`GreenFunctionRayInversion` without appealing to
`MLC.Quadratic.external_ray_map_exists`. -/
axiom green_function_strictMono_along_ray_basin_seam
    (c : ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (h12 : ρ₁ < ρ₂)
    (hG : 0 < green_function c ((ρ₁ : ℂ) * u)) :
    green_function c ((ρ₁ : ℂ) * u) < green_function c ((ρ₂ : ℂ) * u)

end MLC.Quadratic

/-!
Additional high-level axioms used in the MLC strategy live in `Mlc/AxiomsMainConjecture.lean`
to avoid import cycles with the low-level puzzle lemmas.
-/
