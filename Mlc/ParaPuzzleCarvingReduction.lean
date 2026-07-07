import Mlc.ParaPuzzleConnectivity
import Mlc.Quadratic.Complex.Bottcher.Slodkowski

/-!
# Carving-motion reduction of frontier axiom A

Frontier axiom A
(`MLC.green_sublevel_translate_inter_mandelbrot_connected`) asserts

  `IsConnected ({c' | G_c(c'-c) < (1/2)^n} ∩ MandelbrotSet)`.

The left factor `{c' | G_c(c'-c) < (1/2)^n}` is **already proved connected**
(`green_sublevel_translate_connected`, from core axioms only — it is the
translate of the connected dynamical Green sublevel). Hence the *entire* residual
content of axiom A is the intersection `∩ MandelbrotSet`.

This file records the sharpest conditional reduction obtained so far: axiom A
follows from the existence of a **single space-holomorphic self-motion** of the
(proved-connected) parameter translate whose time-`t` image is exactly the
intersection with `M`. This is the Douady–Hubbard "wringing"/tubing map carving
out `M`; naming it isolates the one irreducible ingredient without adding axioms.
-/

namespace MLC

open MLC.Quadratic Complex Topology Set Metric

/-- **Carving-motion hypothesis for a single parameter puzzle piece.** There is a
space-holomorphic motion of the (proved-connected) parameter translate
`{c' | G_c(c'-c) < (1/2)^n}` whose image, at some time in the unit disk, is exactly
that translate intersected with the Mandelbrot set. Morally this is the
Douady–Hubbard parameter↔dynamical wringing map restricted to the puzzle piece. -/
def ParaPieceCarvedByMotion (c : ℂ) (n : ℕ) : Prop :=
  ∃ (H : Quadratic.SpaceHolomorphicMotion
          {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}) (t : ℂ),
    t ∈ Metric.ball (0 : ℂ) 1 ∧
      H.f t '' {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet

/-- **Sharpest conditional reduction of frontier axiom A.** For `c ∈ M`, if the
parameter puzzle piece is carved out of the (proved-connected) translate by a
space-holomorphic motion, then the intersection with `M` is connected.

Compared to `ParaPieceIsMotionImage`, the connected reference set is no longer an
existential unknown: it is the concrete translate
`{c' | G_c(c'-c) < (1/2)^n}`, whose connectivity is discharged unconditionally by
`green_sublevel_translate_connected`. The only remaining input is the carving
motion itself. -/
theorem isConnected_greenSublevel_inter_mandelbrot_of_carvedByMotion
    {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ)
    (h : ParaPieceCarvedByMotion c n) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  obtain ⟨H, t, ht, himg⟩ := h
  rw [← himg]
  exact H.isConnected_image ht (green_sublevel_translate_connected hc n)

end MLC
