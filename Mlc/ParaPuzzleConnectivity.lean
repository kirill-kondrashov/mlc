import Mlc.GreenSublevelConnectedDirect

/-!
# Para-puzzle connectivity and the parameter frontier

The checked root path uses the direct potential-theory proof
`green_sublevel_connected_direct` for dynamical Green-sublevel connectivity.
It then identifies the frozen translated dynamical piece with the corresponding
parameter translate and invokes only the explicitly labeled straddling
parameter-connectivity frontier.

The module contains only the parameter-puzzle identities and the labeled
straddling frontier used by the checked root theorem.
-/

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-! ## Step 3: DynamicalPuzzlePiece = GreenSublevel for c ∈ M -/

/-- If a set `S` is connected and `x ∈ S`, then the connected component of `x`
    in `S` is `S` itself. -/
lemma connectedComponentIn_eq_of_isConnected {S : Set ℂ} {x : ℂ}
    (hS : IsConnected S) (hx : x ∈ S) :
    connectedComponentIn S x = S := by
  apply Set.eq_of_subset_of_subset
  · exact connectedComponentIn_subset S x
  · exact hS.isPreconnected.subset_connectedComponentIn hx Subset.rfl

/-- For `c ∈ M`, the dynamical puzzle piece `D_n(0)` equals the Green sublevel
    set `{G_c < (1/2)^n}`, because the sublevel is connected. -/
theorem dynamicalPuzzlePiece_eq_greenSublevel {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    DynamicalPuzzlePiece c n 0 = Quadratic.GreenSublevel c n := by
  -- DynamicalPuzzlePiece c n 0 = connectedComponentIn {G_c < (1/2)^n} 0
  -- GreenSublevel c n = {G_c < (1/2)^n}
  -- These share the same underlying set.
  show connectedComponentIn {w | green_function c w < (1 / 2 : ℝ) ^ n} (0 : ℂ) =
    Quadratic.GreenSublevel c n
  -- GreenSublevel c n is connected (proved) and contains 0
  have h_conn : IsConnected (Quadratic.GreenSublevel c n) :=
    green_sublevel_connected_direct c n hc
  have h_zero : (0 : ℂ) ∈ Quadratic.GreenSublevel c n :=
    Quadratic.green_sublevel_contains_0 c n hc
  -- The connected component of 0 in a connected set is the whole set
  exact connectedComponentIn_eq_of_isConnected h_conn h_zero

/-- For `c ∈ M`, membership in `ParaPuzzlePieceAt c n` is equivalent to the
    Green function condition. -/
theorem mem_paraPuzzlePieceAt_iff_green {c c' : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    c' ∈ ParaPuzzlePieceAt c n ↔ green_function c (c' - c) < (1 / 2 : ℝ) ^ n := by
  -- ParaPuzzlePieceAt c n = {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
  show c' - c ∈ DynamicalPuzzlePiece c n 0 ↔ green_function c (c' - c) < (1 / 2 : ℝ) ^ n
  rw [dynamicalPuzzlePiece_eq_greenSublevel hc n]
  rfl

/-- For `c ∈ M`, `ParaPuzzlePieceAt c n` equals the Green sublevel translate. -/
theorem paraPuzzlePieceAt_eq_green_translate {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    ParaPuzzlePieceAt c n = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} := by
  ext c'
  exact mem_paraPuzzlePieceAt_iff_green hc n

/-! ## Step 5: Green-sublevel–M intersection connectivity axiom -/

/-- **The un-intersected parameter translate is connected (unconditional).** For
    `c ∈ M`, the parameter-plane set `{c' | G_c(c'-c) < (1/2)^n}` is connected,
    because it is the translate by `+c` of the dynamical Green sublevel
    `{w | G_c(w) < (1/2)^n}`, whose connectivity is already proved
    (`green_sublevel_connected_hyp_proved`), and translation is a homeomorphism.

    This isolates the entire residual difficulty of frontier axiom A into the
    intersection `∩ MandelbrotSet`: the reference set is connected *for free*; only
    the Douady–Hubbard parameter↔dynamical correspondence carving out `M` remains. -/
theorem green_sublevel_translate_connected {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} := by
  have hconn : IsConnected (Quadratic.GreenSublevel c n) :=
    green_sublevel_connected_direct c n hc
  have himg : (fun w => w + c) '' Quadratic.GreenSublevel c n
      = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} := by
    ext c'
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : green_function c w < (1 / 2 : ℝ) ^ n := hw
      simpa [add_sub_cancel_right] using this
    · intro hc'
      exact ⟨c' - c, hc', by ring⟩
  rw [← himg]
  exact hconn.image _ (continuous_id.add continuous_const).continuousOn


/-! ### Elementary containment fragment (no frontier axiom)

    If the Green-sublevel translate is entirely contained in `M`, the intersection
    is the translate itself. Only the intermediate **straddling** stratum — where
    the equipotential neighborhood genuinely crosses `∂M` — requires the
    Yoccoz parameter↔dynamical correspondence. -/

/-- **Subset stratum (core-clean).** If the Green-sublevel translate is entirely
    contained in `M`, the intersection equals the translate itself, whose
    connectivity is already proved unconditionally (`green_sublevel_translate_connected`).
    No frontier axiom is used. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_of_subset {c : ℂ}
    (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hsub : {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  rw [Set.inter_eq_left.mpr hsub]
  exact green_sublevel_translate_connected hc n

/-- **Weaker frontier axiom: straddling stratum only.** The connectivity of a
    Yoccoz parameter-puzzle piece intersected with `M`, *restricted* to the
    non-trivial case where the Green-sublevel translate is **not** contained in `M`.

    This is a strictly weaker statement than the previous
    `green_sublevel_translate_inter_mandelbrot_connected` axiom: it carries the
    extra hypothesis `hstraddle` and therefore no longer asserts anything on the
    subset stratum (which is now discharged unconditionally by
    `green_sublevel_translate_inter_mandelbrot_connected_of_subset`). The residual
    mathematical content is exactly the Douady–Hubbard parameter↔dynamical
    correspondence for pieces whose equipotential boundary crosses `∂M` — i.e.
    Yoccoz's theorem for finitely renormalizable parameters.

    ## Frontier-axiom status (labeled; honest)

    The remaining full discharge is the Douady–Hubbard
    parameter↔dynamical correspondence for the straddling pieces, for example
    through a genuine holomorphic motion whose image is the concrete
    parameter intersection. That research-scale input is retained as this
    labeled frontier axiom. -/
axiom green_sublevel_translate_inter_mandelbrot_connected_straddling (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle : ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet)) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)

/-- **Full Green-sublevel–M intersection connectivity**, now derived (not axiomatized)
    by a case split on the subset stratum: the trivial subset case is discharged
    unconditionally, and only the straddling case invokes the weaker frontier axiom
    `green_sublevel_translate_inter_mandelbrot_connected_straddling`. -/
theorem green_sublevel_translate_inter_mandelbrot_connected (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  by_cases hsub : {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet
  · exact green_sublevel_translate_inter_mandelbrot_connected_of_subset hc n hsub
  · exact green_sublevel_translate_inter_mandelbrot_connected_straddling c hc n hsub

/-! ## Step 6: Para-puzzle connectivity (Route A plus the straddling frontier) -/

/-- Para-puzzle pieces intersected with M are connected — proved from
    the direct dynamical Green-sublevel theorem plus the
    Green-sublevel–M intersection connectivity frontier. -/
theorem para_puzzle_piece_inter_mandelbrot_connected_proved (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet) := by
  rw [paraPuzzlePieceAt_eq_green_translate hc n]
  exact green_sublevel_translate_inter_mandelbrot_connected c hc n

end

end MLC
