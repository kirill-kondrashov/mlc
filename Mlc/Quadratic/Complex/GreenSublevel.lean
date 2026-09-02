import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Mlc.ParaPuzzleContainment

namespace MLC.Quadratic

open Complex Set

noncomputable section

/-- The dynamical Green sublevel used at puzzle depth `n`. -/
def GreenSublevel (c : ℂ) (n : ℕ) : Set ℂ :=
  {w | green_function c w < (1 / 2 : ℝ) ^ n}

/-- The boundary of the depth-`n` Green sublevel used in the puzzle construction. -/
def PuzzleBoundary (c : ℂ) (n : ℕ) : Set ℂ :=
  frontier (GreenSublevel c n)

/-- If `c ∈ M`, then the critical point lies in every Green sublevel. -/
theorem green_sublevel_contains_0 (c : ℂ) (n : ℕ) (hc : c ∈ MandelbrotSet) :
    0 ∈ GreenSublevel c n := by
  have h0K : (0 : ℂ) ∈ K c := hc
  have h0 : green_function c 0 = 0 :=
    (green_function_eq_zero_iff_mem_K c 0).2 h0K
  exact by
    simp only [GreenSublevel, mem_setOf_eq, h0]
    positivity

/-- If `c ∈ M`, then the parameter center lies in every Green sublevel. -/
theorem green_sublevel_contains_c (c : ℂ) (n : ℕ) (hc : c ∈ MandelbrotSet) :
    c ∈ GreenSublevel c n := by
  have hcK : c ∈ K c := mem_K_of_mandelbrot hc
  have hc0 : green_function c c = 0 :=
    (green_function_eq_zero_iff_mem_K c c).2 hcK
  exact by
    simp only [GreenSublevel, mem_setOf_eq, hc0]
    positivity

/-- Connectivity data for Green sublevels on the Mandelbrot set. -/
structure GreenSublevelConnectedHyp : Prop where
  connected :
    ∀ (c : ℂ) (n : ℕ), c ∈ MandelbrotSet → IsConnected (GreenSublevel c n)

end

end MLC.Quadratic
