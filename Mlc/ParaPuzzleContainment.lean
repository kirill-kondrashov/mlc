import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Yoccoz.Quadratic.Complex.PuzzleLemmas
import Mlc.FilledJuliaConnected

/-!
# M ⊆ ParaPuzzlePiece n

We prove that every parameter `c ∈ M` belongs to the Yoccoz para-puzzle piece
`ParaPuzzlePiece n` for every depth `n`. This uses:

1. `c ∈ M ⟹ c ∈ K(c)` (the orbit of c is the tail of the orbit of 0).
2. `K(c)` is connected (`filled_julia_set_connected`).
3. `K(c) ⊆ {w | G(c,w) < (1/2)^n}` (Green's function vanishes on K).
4. Connected subset inclusion into `connectedComponentIn`.

This is the foundation for Route C: replacing the incorrect `ParaPuzzlePieceAt`
translate definition with proper Yoccoz para-puzzle pieces.
-/

namespace MLC.Quadratic

open Set Topology

/-- The orbit of `c` under `z² + c` equals the orbit of `0` shifted by one step. -/
lemma orbit_param_eq_orbit_zero_succ (c : ℂ) (n : ℕ) :
    orbit c c n = orbit c 0 (n + 1) := by
  simp only [orbit]
  rw [Function.iterate_succ_apply]
  simp [fc]

/-- If `c ∈ M` (the orbit of 0 is bounded), then the orbit of `c` is also bounded. -/
lemma boundedOrbit_param_of_mandelbrot {c : ℂ} (hc : c ∈ MandelbrotSet) :
    boundedOrbit c c := by
  obtain ⟨B, hB⟩ := hc
  exact ⟨B, fun n => by rw [orbit_param_eq_orbit_zero_succ]; exact hB (n + 1)⟩

/-- If `c ∈ M`, then `c ∈ K(c)`. -/
lemma mem_K_of_mandelbrot {c : ℂ} (hc : c ∈ MandelbrotSet) : c ∈ K c :=
  boundedOrbit_param_of_mandelbrot hc

/-- `K(c)` is contained in the sublevel set `{w | G(c,w) < (1/2)^n}`. -/
lemma K_subset_green_sublevel (c : ℂ) (n : ℕ) :
    K c ⊆ {w | green_function c w < (1 / 2 : ℝ) ^ n} := by
  intro z hz
  simp only [mem_setOf_eq]
  have h0 : green_function c z = 0 := (green_function_eq_zero_iff_mem_K c z).mpr hz
  rw [h0]
  exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n

/-- `K(c)` is contained in `DynamicalPuzzlePiece c n 0` when `c ∈ M`. -/
lemma K_subset_dynamicalPuzzlePiece {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    K c ⊆ DynamicalPuzzlePiece c n 0 := by
  have hK_conn := filled_julia_set_connected hc
  have h0_in_K : (0 : ℂ) ∈ K c := hc
  have hK_sub := K_subset_green_sublevel c n
  exact hK_conn.isPreconnected.subset_connectedComponentIn h0_in_K hK_sub

/-- Every `c ∈ M` belongs to `DynamicalPuzzlePiece c n 0`. -/
theorem mem_dynamicalPuzzlePiece_param {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    c ∈ DynamicalPuzzlePiece c n 0 :=
  K_subset_dynamicalPuzzlePiece hc n (mem_K_of_mandelbrot hc)

/-- Every `c ∈ M` belongs to `ParaPuzzlePiece n` for all `n`. -/
theorem mandelbrot_subset_paraPuzzlePiece {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    c ∈ ParaPuzzlePiece n :=
  mem_dynamicalPuzzlePiece_param hc n

/-- `M ⊆ ParaPuzzlePiece n` as a set inclusion. -/
theorem mandelbrotSet_subset_paraPuzzlePiece (n : ℕ) :
    MandelbrotSet ⊆ ParaPuzzlePiece n :=
  fun _ hc => mandelbrot_subset_paraPuzzlePiece hc n

end MLC.Quadratic
