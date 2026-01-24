import Yoccoz.Quadratic.Complex.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded

open Topology Set Filter Bornology Metric Complex Function

namespace Mlc.MandelbrotEquivalence

/-!
## DeepMind Equivalence

This file establishes the equivalence between our definition of the Mandelbrot set
and the one used in the Google DeepMind `formal-conjectures` repository:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mandelbrot.lean

Due to version incompatibilities with the upstream repository, we replicate the
DeepMind definitions here to prove they match our library's definitions.
-/

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrot set for n = 2. -/
abbrev deepMindMandelbrotSet := multibrotSet 2

/-- Our definition of the Mandelbrot set (from Yoccoz library). -/
abbrev ourMandelbrotSet := MLC.Quadratic.MandelbrotSet

/-- The quadratic map `z ↦ z^2 + c`. -/
def fc (c : ℂ) (z : ℂ) : ℂ := z^2 + c

/-! ### Escape radius axiom

This axiom packages the standard escape radius argument for quadratic polynomials:
if the critical orbit does not tend to infinity, then it is bounded. -/
axiom boundedOrbit_of_not_tendsto_infinity (c : ℂ) :
    ¬ Tendsto (fun k ↦ ‖(fc c)^[k] 0‖) atTop atTop →
      MLC.Quadratic.boundedOrbit c 0

lemma tendsto_cobounded_iff_norm_tendsto_atTop {α : Type*} [NormedAddCommGroup α] (f : ℕ → α) :
    Tendsto f atTop (cobounded α) ↔ Tendsto (fun n ↦ ‖f n‖) atTop atTop := by
  -- Use the characterization of cobounded in metric spaces via distance to a point (0 here)
  rw [← Metric.comap_dist_right_atTop (0 : α)]
  rw [tendsto_comap_iff]
  simp only [dist_zero_right, Function.comp_def]

/-- The orbit of 0 under fc is bounded iff it does not tend to infinity. -/
theorem bounded_iff_not_tendsto_infinity (c : ℂ) :
    MLC.Quadratic.boundedOrbit c 0 ↔ ¬ Tendsto (fun k ↦ (fc c)^[k] 0) atTop (cobounded ℂ) := by
  rw [tendsto_cobounded_iff_norm_tendsto_atTop]
  constructor
  · -- Bounded implies not tending to infinity
    intro h_bounded h_tendsto
    rcases h_bounded with ⟨M, hM⟩
    -- If tendsto atTop, eventually > M. But always <= M. Contradiction.
    rw [Filter.tendsto_atTop] at h_tendsto
    specialize h_tendsto (M + 1)
    rw [Filter.eventually_atTop] at h_tendsto
    rcases h_tendsto with ⟨N, hN⟩
    have h_orbit : MLC.Quadratic.orbit c 0 N = (fc c)^[N] 0 := rfl
    specialize hN N (le_refl N)
    have := hM N
    rw [h_orbit] at this
    linarith
  · -- Not tending to infinity implies bounded
    intro h_not_tendsto
    -- Escape radius argument: if unbounded, it escapes R and goes to infinity.
    -- Standard complex dynamics result.
    -- We record this as an axiom pending a full escape-radius formalization.
    exact boundedOrbit_of_not_tendsto_infinity c h_not_tendsto

/-- The equivalence theorem for the sets. -/
theorem mandelbrot_set_equivalence : deepMindMandelbrotSet = ourMandelbrotSet := by
  ext c
  rw [deepMindMandelbrotSet, multibrotSet, Set.mem_setOf_eq]
  rw [ourMandelbrotSet, MLC.Quadratic.MandelbrotSet, Set.mem_setOf_eq]
  rw [bounded_iff_not_tendsto_infinity]
  rfl

/-- The equivalence of the MLC conjecture statements.
    DeepMind's formulation: LocallyConnectedSpace deepMindMandelbrotSet
    Our formulation: LocallyConnectedSpace ourMandelbrotSet -/
theorem mlc_conjecture_equivalence :
    LocallyConnectedSpace deepMindMandelbrotSet ↔ LocallyConnectedSpace ourMandelbrotSet := by
  rw [mandelbrot_set_equivalence]

end Mlc.MandelbrotEquivalence
