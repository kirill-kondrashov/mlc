import Mlc.GreenSublevelConnected
import Mlc.ParaPuzzleContainment
import Mlc.Quadratic.Complex.PuzzleLemmas2
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory

/-!
# Para-puzzle connectivity from Böttcher infrastructure

This file proves `ParaPuzzlePieceInterMandelbrotConnectedData` (and hence
`para_puzzle_piece_inter_mandelbrot_connected`) from two clean axioms:

1. **Basin injectivity** (`proxy_bottcher_map_inj_on_basin_axiom`):
   For every parameter `c`, the proxy Böttcher map is injective on the basin
   of infinity. This is a standard fact in holomorphic dynamics: for connected
   K(c), the Böttcher coordinate is conformal on the basin.

2. **Green-sublevel–M intersection connectivity**
   (`green_sublevel_translate_inter_mandelbrot_connected`):
   For `c ∈ M` and every `n`, the set
   `{c' | G_c(c' − c) < (1/2)^n} ∩ M` is connected.
   This is the core content of the Yoccoz puzzle connectivity theorem.

The proof chain:
- Basin injectivity + exterior ray surjectivity (from `external_ray_map_exists`)
  → `GreenSublevelConnectedHyp` (Green sublevels are connected for c ∈ M)
  → `DynamicalPuzzlePiece c n 0 = GreenSublevel c n` for c ∈ M
  → `ParaPuzzlePieceAt c n = {c' | G_c(c' − c) < (1/2)^n}`
  → `ParaPuzzlePieceAt c n ∩ M` is connected (by axiom 2)
-/

namespace MLC

open Quadratic Complex Topology Set Filter

noncomputable section

/-! ## Step 1: Böttcher surjectivity from `external_ray_map_exists` -/

/-- The proxy Böttcher map is surjective onto `{w | 1 < ‖w‖}` from the
    `bottcher_domain`. This follows from the right-inverse property of the
    external ray map. -/
theorem bottcher_surj_from_ray_map :
    ∀ c w, 1 < ‖w‖ → w ∈ Quadratic.proxy_bottcher_map c '' Quadratic.bottcher_domain c := by
  intro c w hw
  -- external_ray_map c w is in bottcher_domain by construction
  have h_mem : Quadratic.external_ray_map c w ∈ Quadratic.bottcher_domain c :=
    ⟨w, hw, rfl⟩
  -- proxy_bottcher_map c (external_ray_map c w) = w by right inverse
  have h_inv : Quadratic.proxy_bottcher_map c (Quadratic.external_ray_map c w) = w :=
    Quadratic.external_ray_map_right_inverse c w hw
  exact ⟨Quadratic.external_ray_map c w, h_mem, h_inv⟩

/-! ## Step 2: Basin injectivity axiom -/

/-- For every parameter `c ∈ M`, the proxy Böttcher map is injective on the
    basin of infinity.

    This is now a **theorem**, not an axiom. Because `proxy_bottcher_map` is the
    *radial* proxy `(z/‖z‖)·exp(green c z)`, injectivity is elementary
    (`proxy_bottcher_map_injOn_nonzero_basin_of_green_ray_strictMono`): it reduces
    to strict monotonicity of the Green function along origin-rays
    (`green_function_strictMono_along_ray_basin_seam`), together with `0 ∉ basin`
    for `c ∈ M` (the critical point stays in `K(c)`). -/
theorem proxy_bottcher_map_inj_on_basin_of_mem_mandelbrot (c : ℂ)
    (hc : c ∈ MLC.Quadratic.MandelbrotSet) :
    Set.InjOn (Quadratic.proxy_bottcher_map c) (Quadratic.basin_of_infinity c) := by
  have hmono : ∀ (u : ℂ), ‖u‖ = 1 → ∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₁ < ρ₂ →
      0 < MLC.Quadratic.green_function c ((ρ₁ : ℂ) * u) →
      MLC.Quadratic.green_function c ((ρ₁ : ℂ) * u)
        < MLC.Quadratic.green_function c ((ρ₂ : ℂ) * u) :=
    fun u hu => Quadratic.green_function_strictMono_along_ray_basin_seam c u hu
  have hbase :=
    proxy_bottcher_map_injOn_nonzero_basin_of_green_ray_strictMono c hmono
  have h0K : (0 : ℂ) ∈ MLC.Quadratic.K c := hc
  have h0 : (0 : ℂ) ∉ Quadratic.basin_of_infinity c := by
    rw [Quadratic.basin_eq_compl_K]
    simpa using h0K
  intro z hz w hw hzw
  refine hbase ⟨hz, ?_⟩ ⟨hw, ?_⟩ hzw
  · exact fun h => h0 (h ▸ hz)
  · exact fun h => h0 (h ▸ hw)

/-! ## Step 3: Green sublevel connectivity (proved) -/

/-- Green sublevel sets `{G_c < (1/2)^n}` are connected for `c ∈ M`.
    Proved from basin injectivity + exterior ray surjectivity. -/
theorem green_sublevel_connected_hyp_proved : Quadratic.GreenSublevelConnectedHyp :=
  green_sublevel_connected_onM

/-! ## Step 4: DynamicalPuzzlePiece = GreenSublevel for c ∈ M -/

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
    green_sublevel_connected_hyp_proved.connected c n hc
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
    green_sublevel_connected_hyp_proved.connected c n hc
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


/-! ### Elementary containment fragments (no frontier axiom)

    The intersection `{c' | G_c(c'-c) < (1/2)ⁿ} ∩ M` is connected *for free* in the
    two extreme strata, where the Green-sublevel translate and `M` are nested. Only
    the intermediate **straddling** stratum — where the equipotential neighborhood
    genuinely crosses `∂M` — requires the Yoccoz parameter↔dynamical correspondence.
    These two lemmas carve those trivial strata out of the frontier axiom. -/

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

/-- **Superset stratum (off the `mlc_conjecture` path).** If `M` is contained in the
    Green-sublevel translate, the intersection equals `M`, connected by
    `mandelbrot_set_connected`. This documents the second trivial stratum; it is
    **not** consumed by the main derivation below, so it does not add
    `mandelbrot_set_connected` to the MLC frontier. -/
theorem green_sublevel_translate_inter_mandelbrot_connected_of_superset {c : ℂ}
    (n : ℕ)
    (hsup : MandelbrotSet ⊆ {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  rw [Set.inter_eq_right.mpr hsup]
  exact mandelbrot_set_connected

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

    One of the two remaining non-core frontier axioms (Tier C). Two discharge
    routes were investigated:

    * **Metric route (Ahlfors/Schwarz–Pick λ-lemma).** Fully built as sound
      standalone mathematics (`AhlforsSchwarz`, `UltrahyperbolicMetric`,
      `UltrahyperbolicPullback`, `UltrahyperbolicDistance`), but it hits a
      *completeness obstruction*: the constructed curvature `≤ -1` metric on
      `ℂ∖{0,1}` is not complete (density `∼ ‖w-1‖^{-5/6}`, finite radial distance
      to a puncture), so the two-trajectory Schwarz–Pick bound does not force
      continuity-in-space. Correct but insufficient.

    * **Böttcher route (C).** Realize the moving equipotential boundaries through
      the space-holomorphic parametrization `z = Φ_c⁻¹(ω)`, making the residual
      continuity free (`LambdaLemma.isConnected_image_of_differentiableOn`). The
      base case — a genuine near-infinity two-variable holomorphic Böttcher family
      with fiber-holo (z), param-holo (c) and joint continuity in `(c,z)` — is
      built and axiom-clean (`BottcherParamHolo`,
      `Quadratic.logSeriesNearInfinityParameterFamily`).

    Remaining for a full discharge (Yoccoz-scale, deliberately NOT pursued): the
    full-basin monodromy-coherent coordinate, the holomorphic inverse `Φ_c⁻¹`, a
    nontrivial puzzle-boundary `HolomorphicMotion`, and the parameter↔dynamical
    correspondence. Kept as a labeled frontier axiom pending that formalization. -/
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

/-! ## Step 6: Para-puzzle connectivity (proved from axioms 1 + 2) -/

/-- Para-puzzle pieces intersected with M are connected — proved from
    basin injectivity + Green-sublevel–M intersection connectivity. -/
theorem para_puzzle_piece_inter_mandelbrot_connected_proved (c : ℂ)
    (hc : c ∈ MandelbrotSet) (n : ℕ) :
    IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet) := by
  rw [paraPuzzlePieceAt_eq_green_translate hc n]
  exact green_sublevel_translate_inter_mandelbrot_connected c hc n

/-- The full data package for para-puzzle connectivity, proved from
    Böttcher infrastructure. -/
theorem para_puzzle_connectivity_data_proved :
    Quadratic.ParaPuzzlePieceInterMandelbrotConnectedData := by
  intro c hc n
  exact para_puzzle_piece_inter_mandelbrot_connected_proved c hc n

/-- Transport witness hypothesis, proved from Böttcher infrastructure. -/
theorem para_puzzle_transport_witness_hyp_proved :
    Quadratic.ParaPuzzleTransportWitnessHyp := by
  refine ⟨?_⟩
  intro c hc n
  exact ⟨ParaPuzzlePieceAt c n ∩ MandelbrotSet,
    para_puzzle_piece_inter_mandelbrot_connected_proved c hc n,
    rfl⟩

end

end MLC
