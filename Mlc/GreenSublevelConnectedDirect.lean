import Mlc.Quadratic.Complex.GreenHarmonic
import Mlc.Quadratic.Complex.HarmonicMinimumPrinciple
import Mlc.Quadratic.Complex.PuzzleBoundaryMotion
import Mlc.Quadratic.Complex.ParaPuzzleBasis

/-!
# Direct proof that Green sublevel sets are connected (Route A)

This file discharges the connectivity of the Green sublevel sets
`GreenSublevel c n = {z | G_c z < (1/2)ⁿ}` for `c ∈ M` by a *direct*
potential-theory argument, replacing the earlier route through the radial-proxy
Böttcher machinery (which relied on the unsound axioms
`extended_ray_map_free_continuous` and
`green_function_strictMono_along_ray_basin_seam`).

The argument is the classical minimum-principle proof:

* every connected component `W` of the (open, bounded) sublevel set `S` that is
  *disjoint from* the filled Julia set `K_c` lies in the basin of infinity, where
  `G_c` is harmonic (`green_function_harmonicOnNhd_basin`);
* on `W`, `G_c < (1/2)ⁿ`, while on the (nonempty) frontier of `W` we have
  `G_c ≥ (1/2)ⁿ`; the interior minimum forces `G_c` to be constant on `W`
  (`HarmonicOnNhd.eqOn_const_of_isMinOn`), contradicting the frontier values.

Hence every component of `S` meets the connected set `K_c ⊆ S`, so `S` is
connected.
-/

namespace MLC

open Quadratic Complex Topology Set Metric InnerProductSpace

/-- The Green sublevel set is open. -/
lemma isOpen_greenSublevel (c : ℂ) (n : ℕ) : IsOpen (GreenSublevel c n) :=
  isOpen_lt (continuous_green_function c) continuous_const

/-- **Route-A key lemma.**  For `c ∈ M`, every connected component of the Green
sublevel set meets the filled Julia set `K_c`. -/
lemma connectedComponentIn_greenSublevel_inter_K_nonempty
    (c : ℂ) (n : ℕ) (_hc : c ∈ MandelbrotSet) {y : ℂ}
    (hy : y ∈ GreenSublevel c n) :
    (connectedComponentIn (GreenSublevel c n) y ∩ K c).Nonempty := by
  have hcont : Continuous (green_function c) := continuous_green_function c
  set S := GreenSublevel c n with hSdef
  have hSopen : IsOpen S := isOpen_greenSublevel c n
  have hSbdd : Bornology.IsBounded S := bounded_sublevel_green_function c ((1 / 2) ^ n)
  set W := connectedComponentIn S y with hWdef
  have hWsub : W ⊆ S := connectedComponentIn_subset S y
  have hWopen : IsOpen W := hSopen.connectedComponentIn
  have hyW : y ∈ W := mem_connectedComponentIn hy
  have hWne : W.Nonempty := ⟨y, hyW⟩
  have hWbdd : Bornology.IsBounded W := hSbdd.subset hWsub
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  -- `W` is disjoint from `K_c`, hence contained in the basin of infinity.
  have hWbasin : W ⊆ Quadratic.basin_of_infinity c := by
    rw [Quadratic.basin_eq_compl_K]
    intro z hz hzK
    exact (Set.eq_empty_iff_forall_notMem.1 hempty z) ⟨hz, hzK⟩
  -- `G_c` is harmonic on `W`.
  have hHarm : HarmonicOnNhd (green_function c) W :=
    fun p hp => green_function_harmonicAt_of_mem_basin c (hWbasin hp)
  -- The closure of `W` is compact and nonempty; `G_c` attains a minimum there.
  have hclCompact : IsCompact (closure W) := hWbdd.isCompact_closure
  have hclNe : (closure W).Nonempty := hWne.closure
  obtain ⟨x₀, hx₀cl, hx₀min⟩ := hclCompact.exists_isMinOn hclNe hcont.continuousOn
  -- Points of `closure W` that lie in `S` already lie in `W`.
  have hclInterS : closure W ∩ S ⊆ W := by
    intro x hx
    obtain ⟨hxcl, hxS⟩ := hx
    have hW'open : IsOpen (connectedComponentIn S x) := hSopen.connectedComponentIn
    have hxW' : x ∈ connectedComponentIn S x := mem_connectedComponentIn hxS
    obtain ⟨p, hpW', hpW⟩ := mem_closure_iff.1 hxcl _ hW'open hxW'
    have h1 : connectedComponentIn S x = connectedComponentIn S p :=
      connectedComponentIn_eq hpW'
    have h2 : connectedComponentIn S y = connectedComponentIn S p :=
      connectedComponentIn_eq hpW
    show x ∈ connectedComponentIn S y
    rw [h2, ← h1]; exact hxW'
  -- `W` has a nonempty frontier: otherwise it would be clopen, hence all of `ℂ`.
  have hbdry : ∃ x, x ∈ closure W ∧ x ∉ W := by
    by_contra hcon
    push_neg at hcon
    have hWclosed : IsClosed W := by
      rw [← closure_subset_iff_isClosed]; exact fun x hx => hcon x hx
    have hUniv : W = Set.univ := (IsClopen.eq_univ ⟨hWclosed, hWopen⟩ hWne)
    have hbd : Bornology.IsBounded (Set.univ : Set ℂ) := hUniv ▸ hWbdd
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbd
    have h0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg (0 : ℂ)) (hR 0 (mem_univ _))
    have hlt := hR ((R + 1 : ℝ) : ℂ) (mem_univ _)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at hlt
    linarith
  obtain ⟨xb, hxb_cl, hxb_notW⟩ := hbdry
  have hxb_notS : xb ∉ S := fun hxbS => hxb_notW (hclInterS ⟨hxb_cl, hxbS⟩)
  have hxb_ge : (1 / 2 : ℝ) ^ n ≤ green_function c xb :=
    not_lt.1 (fun h => hxb_notS h)
  -- The minimum is attained inside `W` (frontier values are `≥ (1/2)ⁿ`).
  have hgy : green_function c y < (1 / 2 : ℝ) ^ n := hy
  have hx₀ltε : green_function c x₀ < (1 / 2 : ℝ) ^ n :=
    lt_of_le_of_lt (isMinOn_iff.1 hx₀min y (subset_closure hyW)) hgy
  have hx₀W : x₀ ∈ W := by
    by_contra hx₀notW
    have hx₀notS : x₀ ∉ S := fun h => hx₀notW (hclInterS ⟨hx₀cl, h⟩)
    have : (1 / 2 : ℝ) ^ n ≤ green_function c x₀ :=
      not_lt.1 (fun h => hx₀notS h)
    linarith
  -- `G_c` is constant on `W`, hence on its closure, contradicting the frontier.
  have hminW : ∀ z ∈ W, green_function c x₀ ≤ green_function c z :=
    fun z hz => isMinOn_iff.1 hx₀min z (subset_closure hz)
  have hEqOn : Set.EqOn (green_function c) (fun _ => green_function c x₀) W :=
    HarmonicOnNhd.eqOn_const_of_isMinOn hWopen isPreconnected_connectedComponentIn
      hHarm hx₀W hminW
  have hEqCl : Set.EqOn (green_function c) (fun _ => green_function c x₀) (closure W) :=
    hEqOn.closure hcont continuous_const
  have hxb_eq : green_function c xb = green_function c x₀ := hEqCl hxb_cl
  rw [hxb_eq] at hxb_ge
  linarith

/-- **Route A.**  For `c ∈ M`, the Green sublevel set `{z | G_c z < (1/2)ⁿ}` is
connected. -/
theorem green_sublevel_connected_direct (c : ℂ) (n : ℕ)
    (hc : c ∈ MandelbrotSet) :
    IsConnected (GreenSublevel c n) := by
  have hK_conn : IsConnected (K c) := filled_julia_set_connected hc
  have hK_sub : K c ⊆ GreenSublevel c n := by
    intro z hz
    have hz0 : green_function c z = 0 := (green_function_eq_zero_iff_mem_K c z).2 hz
    show green_function c z < (1 / 2 : ℝ) ^ n
    rw [hz0]; positivity
  obtain ⟨k0, hk0⟩ := hK_conn.nonempty
  have hk0S : k0 ∈ GreenSublevel c n := hK_sub hk0
  refine ⟨⟨k0, hk0S⟩, ?_⟩
  apply isPreconnected_of_forall k0
  intro y hy
  obtain ⟨k, hkW, hkK⟩ :=
    connectedComponentIn_greenSublevel_inter_K_nonempty c n hc hy
  refine ⟨connectedComponentIn (GreenSublevel c n) y ∪ K c,
    Set.union_subset (connectedComponentIn_subset _ _) hK_sub,
    Or.inr hk0, Or.inl (mem_connectedComponentIn hy), ?_⟩
  exact IsPreconnected.union k hkW hkK isPreconnected_connectedComponentIn
    hK_conn.isPreconnected

end MLC
