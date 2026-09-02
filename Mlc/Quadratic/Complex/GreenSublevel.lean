import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green

namespace MLC.Quadratic

open Complex Set

noncomputable section

/-- The dynamical Green sublevel used at puzzle depth `n`. -/
def GreenSublevel (c : ℂ) (n : ℕ) : Set ℂ :=
  {w | green_function c w < (1 / 2 : ℝ) ^ n}

/-- If `c ∈ M`, then the critical point lies in every Green sublevel. -/
theorem green_sublevel_contains_0 (c : ℂ) (n : ℕ) (hc : c ∈ MandelbrotSet) :
    0 ∈ GreenSublevel c n := by
  have h0K : (0 : ℂ) ∈ K c := hc
  have h0 : green_function c 0 = 0 :=
    (green_function_eq_zero_iff_mem_K c 0).2 h0K
  exact by
    simp only [GreenSublevel, mem_setOf_eq, h0]
    positivity

/-- Connectivity data for Green sublevels on the Mandelbrot set. -/
structure GreenSublevelConnectedHyp : Prop where
  connected :
    ∀ (c : ℂ) (n : ℕ), c ∈ MandelbrotSet → IsConnected (GreenSublevel c n)

end

end MLC.Quadratic
