import Mlc.CategoricalTopologicalApproximation
import Mlc.GreenSublevelConnectedDirect

/-!
# Frozen Green-sublevel connectivity and the parameter frontier

This module records the direct potential-theory proof
`green_sublevel_connected_direct` for dynamical Green-sublevel connectivity,
the corresponding frozen parameter translate, and the exact conditional
implications that would follow from a categorical parameter-intersection
datum.

The frozen pieces are a simplified model and are not the graph-cut
parapuzzles of the classical Yoccoz construction. The universal
Green-sublevel/Mandelbrot intersection datum is not assumed here; the
counterexample reference shows that it is false for this model.
-/

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

open Categorical

/-- The dynamical Green sublevel as a topological approximation over the
    ambient parameter plane. -/
def greenSublevelApproximation (c : ℂ) (n : ℕ) : Approximation :=
  ofSet {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}

/-- The Mandelbrot set as a topological approximation over the parameter
    plane. -/
def mandelbrotApproximation : Approximation :=
  ofSet MandelbrotSet

/-- Categorical form of the straddling parameter-connectivity input. -/
def GreenSublevelIntersectionCategoricalData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation →
      ImageConnected
        (intersection (greenSublevelApproximation c n) mandelbrotApproximation)

/-- The original set-theoretic form of the parameter-connectivity input. -/
def GreenSublevelIntersectionSetData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MandelbrotSet) (n : ℕ),
    ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) →
      IsConnected
        ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)

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

/-! ## Step 5: Green-sublevel–M intersection specification -/

/-- **The un-intersected parameter translate is connected (unconditional).** For
    `c ∈ M`, the parameter-plane set `{c' | G_c(c'-c) < (1/2)^n}` is connected,
    because it is the translate by `+c` of the dynamical Green sublevel
    `{w | G_c(w) < (1/2)^n}`, whose connectivity is already proved
    (`green_sublevel_connected_direct`), and translation is a homeomorphism.

    This isolates the residual difficulty of the old frontier specification in
    the intersection `∩ MandelbrotSet`: the reference set is connected *for
    free*; only the Douady–Hubbard parameter↔dynamical correspondence carving
    out `M` remains. -/
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

/-! ### The full Green-sublevel tower is not a classical Yoccoz tower

    Its intersection is the translate of the filled Julia set, rather than the
    center parameter. This is why the remaining intersection specification
    should not be presented as a direct citation of the classical parapuzzle
    theorem. -/

/-- The nested full Green sublevels converge exactly to the translated filled
    Julia set. In particular, these full sublevels are not the shrinking
    graph-cut Yoccoz puzzle pieces. -/
theorem iInter_green_sublevel_translate_eq_translate_filledJulia (c : ℂ) :
    (⋂ n, {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}) =
      (fun z => z + c) '' Quadratic.K c := by
  ext c'
  constructor
  · intro hc'
    have hle : ∀ n, green_function c (c' - c) ≤ (1 / 2 : ℝ) ^ n := by
      intro n
      exact le_of_lt (Set.mem_iInter.mp hc' n)
    have hgreen : green_function c (c' - c) = 0 := by
      have hnonneg : 0 ≤ green_function c (c' - c) :=
        green_function_nonneg c (c' - c)
      by_contra hne
      have hpos : 0 < green_function c (c' - c) :=
        lt_of_le_of_ne hnonneg (Ne.symm hne)
      obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < green_function c (c' - c) := by
        have h_tendsto : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        exact ((tendsto_order.1 h_tendsto).2 (green_function c (c' - c)) hpos).exists
      exact not_lt_of_ge (hle N) hN
    have hK : c' - c ∈ Quadratic.K c :=
      (green_function_eq_zero_iff_mem_K c (c' - c)).1 hgreen
    exact ⟨c' - c, hK, by ring⟩
  · rintro ⟨z, hz, rfl⟩
    refine Set.mem_iInter.mpr ?_
    intro n
    change green_function c ((z + c) - c) < (1 / 2 : ℝ) ^ n
    rw [add_sub_cancel_right, (green_function_eq_zero_iff_mem_K c z).2 hz]
    positivity


/-! ### Elementary containment fragment (no frontier assumption)

    If the Green-sublevel translate is entirely contained in `M`, the intersection
    is the translate itself. Only the intermediate **straddling** stratum — where
    the equipotential neighborhood genuinely crosses `∂M` — requires the
    Yoccoz parameter↔dynamical correspondence. -/

/-- If the Green-sublevel translate is entirely contained in `M`, the
    intersection equals the translate itself. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_of_subset {c : ℂ}
    (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hsub : {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  rw [Set.inter_eq_left.mpr hsub]
  exact green_sublevel_translate_connected hc n

/-! The old straddling statement is retained only as a proposition. The
    full Green-sublevel translate intersected with `M`, *restricted* to the
    non-trivial case where the Green-sublevel translate is **not** contained in
    `M`.

    This is a conditional statement: it carries the
    extra hypothesis `hstraddle` and therefore no longer asserts anything on the
    subset stratum (which is now discharged unconditionally by
    `green_sublevel_translate_inter_mandelbrot_connected_of_subset`). The
    residual mathematical content is an exact phase--parameter realization for
    the full Green-sublevel target. Classical Yoccoz parapuzzles use additional
    ray/equipotential graph data, so this input is not identified with the
    finite-level Yoccoz theorem.

    ## Frontier status (conditional; honest)

    The remaining full discharge is a Douady--Hubbard-style
    parameter↔dynamical correspondence for the straddling full sublevels, for
    example through a genuine holomorphic motion whose image is the concrete
    parameter intersection. That research-scale input is retained only as the
    explicit proposition used by the conditional theorem below. -/
/-- The categorical and set-theoretic parameter-connectivity inputs are
    equivalent. -/
theorem greenSublevelIntersectionCategoricalData_iff :
    GreenSublevelIntersectionCategoricalData ↔
      GreenSublevelIntersectionSetData := by
  constructor
  · intro h c hc n hstraddle
    have hnotfactor :
        ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation := by
      intro hfactor
      exact hstraddle (factorsThrough_ofSet_iff.mp hfactor)
    have hcat := h c hc n hnotfactor
    change _root_.IsConnected
      (image (intersection (greenSublevelApproximation c n) mandelbrotApproximation)) at hcat
    rw [image_intersection] at hcat
    simpa [greenSublevelApproximation, mandelbrotApproximation,
      image_ofSet] using hcat
  · intro h c hc n hnotfactor
    have hstraddle :
        ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) := by
      intro hsub
      exact hnotfactor (factorsThrough_ofSet_iff.mpr hsub)
    have hset := h c hc n hstraddle
    change _root_.IsConnected
      (image (intersection (greenSublevelApproximation c n) mandelbrotApproximation))
    rw [image_intersection]
    simpa [greenSublevelApproximation, mandelbrotApproximation,
      image_ofSet] using hset

/-! The counterexample reference shows that the universal categorical datum
    above is false for the frozen Green-sublevel sets. Any positive result must
    carry an explicit parameter-dynamical hypothesis. -/

/-- Conditional straddling connectivity from the categorical
    Green-intersection datum. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_straddling_of_categorical_data
    (hdata : GreenSublevelIntersectionCategoricalData) (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle : ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet)) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  have hnotfactor :
      ¬ factorsThrough (greenSublevelApproximation c n) mandelbrotApproximation := by
    intro hfactor
    apply hstraddle
    simpa [greenSublevelApproximation, mandelbrotApproximation,
      Quadratic.GreenSublevel] using
      (factorsThrough_ofSet_iff.mp hfactor)
  have hcat := hdata c hc n hnotfactor
  change _root_.IsConnected
    (image (intersection (greenSublevelApproximation c n) mandelbrotApproximation)) at hcat
  rw [image_intersection] at hcat
  simpa [greenSublevelApproximation, mandelbrotApproximation,
    image_ofSet] using hcat

/-! Conditional full Green-sublevel/M connectivity from the categorical
    intersection datum. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_of_categorical_data
    (hdata : GreenSublevelIntersectionCategoricalData) (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  by_cases hsub : {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet
  · exact green_sublevel_translate_inter_mandelbrot_connected_of_subset hc n hsub
  · exact green_sublevel_translate_inter_mandelbrot_connected_straddling_of_categorical_data
      hdata c hc n hsub

/-! ## Step 6: Conditional para-puzzle connectivity -/

/-- Para-puzzle pieces intersected with `M`, conditional on the explicit
    categorical Green-intersection datum. -/
theorem para_puzzle_piece_inter_mandelbrot_connected_of_categorical_data
    (hdata : GreenSublevelIntersectionCategoricalData) (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet) := by
  rw [paraPuzzlePieceAt_eq_green_translate hc n]
  exact green_sublevel_translate_inter_mandelbrot_connected_of_categorical_data
    hdata c hc n

end

end MLC
