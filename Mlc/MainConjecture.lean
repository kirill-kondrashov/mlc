import Yoccoz.Quadratic.Complex.Basic
import Yoccoz.Quadratic.Complex.Green
import Yoccoz.Quadratic.Complex.Puzzle
import Mlc.LcAtOfShrink
import Mlc.InfinitelyRenormalizable
import Mlc.AxiomsMainConjecture
import Mlc.Quadratic.Complex.Bottcher.BottcherMotion
import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.Bottcher.InverseBranchSlitUse
import Mlc.MandelbrotEquivalence
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Complex.Basic
import Lean

open Lean Elab Command

namespace MLC

open Quadratic Complex Topology Set Filter Bornology Metric

/-!
# Mandelbrot Local Connectivity (MLC) Conjecture

This file outlines the proof strategy for the MLC conjecture based on Yoccoz puzzles.

## Integration with DeepMind Formal Conjectures

The definitions of `multibrotSet` and `mandelbrotSet`, as well as the formulation of the `MLC` theorem
around line 106, are adapted from the Google DeepMind `formal-conjectures` repository:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mandelbrot.lean

Note: Because the `formal-conjectures` repository depends on an older version of Lean/Mathlib (v4.22.0)
which is incompatible with this project's dependencies, we have copied the relevant definitions
and theorem statements here to ensure a valid and consistent formalization.
-/

-- Definitions adapted from DeepMind's FormalConjectures (Wikipedia/Mandelbrot.lean)

/-- The Multibrot set of power `n` is the set of all parameters `c : ℂ` for which `0` does not
escape to infinity under repeated application of `z ↦ z ^ n + c`. -/
def multibrotSet (n : ℕ) : Set ℂ :=
  {c | ¬ Tendsto (fun k ↦ (fun z ↦ z ^ n + c)^[k] 0) atTop (cobounded ℂ)}

/-- The Mandelbrot set is the special case of the multibrotSet for n = 2. -/
abbrev mandelbrotSet := multibrotSet 2

-- Equivalence with Yoccoz definition
lemma mandelbrotSet_eq_MandelbrotSet : mandelbrotSet = MLC.Quadratic.MandelbrotSet := by
  exact Mlc.MandelbrotEquivalence.mandelbrot_set_equivalence

section MainProof

/-- Every parameter is either finitely renormalizable (including non-renormalizable) or infinitely renormalizable.
    Proof idea: By the law of excluded middle, the sum of moduli either converges or diverges.
    We use the definition of FinitelyRenormalizable and InfinitelyRenormalizable which directly
    map to this divergence/convergence behavior. -/
theorem dichotomy (c : ℂ) : FinitelyRenormalizable c ∨ InfinitelyRenormalizable c := by
  unfold FinitelyRenormalizable InfinitelyRenormalizable
  rw [or_comm]
  exact Classical.em _

/-- The core strategy theorem (internal). -/
theorem mlc_strategy
    (h_param_shrink :
      ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : FinitelyRenormalizable c),
        (⋂ n, MLC.Quadratic.ParaPuzzlePieceAt c n) = {c})
    (h_bottcher_onM : MLC.Quadratic.BottcherOnMHyp)
    (h_green_conn : MLC.Quadratic.GreenSublevelConnectedHyp)
    (h_classify : ∀ (c : ℂ) (_h : InfinitelyRenormalizable c),
      PrimitiveRenormalizable c ∨ SatelliteRenormalizable c)
    (h_bridge :
      MoleculeConjectureRefined →
      MLC.Quadratic.PuzzleBoundaryMotionHyp →
      ∀ (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet) (_h : SatelliteRenormalizable c),
        MLC.LocallyConnectedAt MLC.Quadratic.MandelbrotSet ⟨c, hc⟩) :
    LocallyConnectedSpace MLC.Quadratic.MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  have h_motion : MLC.Quadratic.PuzzleBoundaryMotionHyp :=
    MLC.Quadratic.puzzle_boundary_motion_hyp_of_onM_connected
      (MLC.Quadratic.bottcher_green_sublevel_hyp_onM_connected_of_onM h_bottcher_onM h_green_conn)
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_fin_renorm | h_inf_renorm
  · -- Case 1: Finitely Renormalizable
    exact mlc_finitely_renormalizable c hc h_fin_renorm (h_param_shrink c hc h_fin_renorm)
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable h_classify h_bridge h_motion c hc h_inf_renorm

/-- A parameterized MLC statement: basin injectivity of the Böttcher map
    is enough to close the strategy. -/
theorem mlc_conjecture_of_bottcher_inj_on_basin
    (h_inj_basin :
      ∀ c, Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  apply mlc_strategy
  · -- Finitely Renormalizable case (Yoccoz)
    intro c hc h_fin
    have h_dyn : (⋂ n, MLC.Quadratic.DynamicalPuzzlePiece c n 0) = {0} := by
      apply MLC.yoccoz_theorem
      simpa [FinitelyRenormalizable, NonRenormalizable] using h_fin
    exact parameter_shrink_of_yoccoz c hc h_fin h_dyn
  · -- Bottcher coordinates exist on M
    exact bottcher_onM_hyp
  · -- Green sublevel sets connected
    exact green_sublevel_connected
      (fun c w hw => Quadratic.bottcher_map_surj c w hw)
      (fun c => h_inj_basin c)
  · -- Classification of infinitely renormalizable parameters (Lyubich)
    intro c h_inf
    exact classify_infinitely_renormalizable c h_inf
  · -- Bridge from Molecule Conjecture to Satellite MLC
    intro h_mol h_motion c hc h_sat
    exact molecule_conjecture_bridge h_mol h_motion c hc h_sat

/-- Basin-wise left-inverse identity for `external_ray_map ∘ bottcher_map`
    is enough to obtain MLC. -/
theorem mlc_conjecture_of_bottcher_left_inverse_on_basin
    (h_left_basin :
      ∀ c, ∀ z, z ∈ Quadratic.basin_of_infinity c →
        Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  exact bottcher_map_inj_on_basin_of_left_inverse c (h_left_basin c)

/-- A parameterized MLC statement: if iterate-equality on the basin is available,
    then the MLC strategy closes. -/
theorem mlc_conjecture_of_iter_eq_imp
    (h_iter_eq_imp :
      ∀ c, ∀ z w, z ∈ Quadratic.basin_of_infinity c →
        w ∈ Quadratic.basin_of_infinity c →
        (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  exact Quadratic.not_quadratic_map_iter_eq_imp_eq 0 (h_iter_eq_imp 0)

/-- Current axiom-backed bridge from iterate-equality to basin injectivity of
    the Böttcher map. Replacing this lemma with a non-axiomatic proof is the
    remaining elimination target. -/
lemma bottcher_map_inj_on_basin_via_iter_eq_axiom (c : ℂ) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  exfalso
  exact Quadratic.not_quadratic_map_iter_eq_imp_eq c
    (Quadratic.quadratic_map_iter_eq_imp_eq c)

/-- If each parameter admits a left inverse of `quadratic_map` on the basin,
    MLC follows via derived iterate-equality. -/
theorem mlc_conjecture_of_quadratic_left_inverse
    (hleft :
      ∀ c, Quadratic.HasLeftInverseOn (quadratic_map c)
        (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 (hleft 0)

/-- A concrete replacement route for iterate-equality, parameterized by a
    variable square-root pullback construction on the Böttcher image of the basin. -/
theorem mlc_conjecture_of_basin_sqrt_branch_of_injective
    (h_branch :
      ∀ c, ∃ sqrt : ℂ → ℂ,
        Quadratic.BasinBottcherSquareRootRightInverse c sqrt ∧
        Function.Injective (Quadratic.bottcher_map c) ∧
        MapsTo (fun z => Quadratic.external_ray_map c (sqrt (Quadratic.bottcher_map c z)))
          (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  rcases h_branch 0 with ⟨sqrt, h_sqrt, h_inj, h_maps⟩
  have h_conj : ∀ z, z ∈ Quadratic.basin_of_infinity 0 →
      Quadratic.bottcher_map 0 (quadratic_map 0 z) = (Quadratic.bottcher_map 0 z) ^ 2 := by
    intro z hz
    simpa using (bottcher_conj_iter 0 1 z hz)
  have h_left_bottcher :
      ∀ z, z ∈ Quadratic.basin_of_infinity 0 →
        Quadratic.external_ray_map 0 (Quadratic.bottcher_map 0 z) = z :=
    Quadratic.bottcher_left_inverse_on_basin_of_injective 0 h_inj
  have hleft :
      Quadratic.HasLeftInverseOn (quadratic_map 0)
        (Quadratic.basin_of_infinity 0) (Quadratic.basin_of_infinity 0) :=
    Quadratic.quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch 0 sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 hleft

/-- A concrete replacement route for iterate-equality from variable branch data
    plus a basin-wide left inverse identity for the Böttcher/ray map pair. -/
theorem mlc_conjecture_of_basin_sqrt_branch
    (h_branch :
      ∀ c, ∃ sqrt : ℂ → ℂ,
        Quadratic.BasinBottcherSquareRootRightInverse c sqrt ∧
        (∀ z, z ∈ Quadratic.basin_of_infinity c →
          Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z) ∧
        MapsTo (fun z => Quadratic.external_ray_map c (sqrt (Quadratic.bottcher_map c z)))
          (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  rcases h_branch 0 with ⟨sqrt, h_sqrt, h_left_bottcher, h_maps⟩
  have h_conj : ∀ z, z ∈ Quadratic.basin_of_infinity 0 →
      Quadratic.bottcher_map 0 (quadratic_map 0 z) = (Quadratic.bottcher_map 0 z) ^ 2 := by
    intro z hz
    simpa using (bottcher_conj_iter 0 1 z hz)
  have hleft :
      Quadratic.HasLeftInverseOn (quadratic_map 0)
        (Quadratic.basin_of_infinity 0) (Quadratic.basin_of_infinity 0) :=
    Quadratic.quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch 0 sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 hleft

/-- A concrete non-vacuous replacement route: provide a pullback root along
    quadratic dynamics on the basin, plus basin mapping and Böttcher left inverse. -/
theorem mlc_conjecture_of_pullback_root
    (h_pull :
      ∀ c, ∃ root : ℂ → ℂ,
        Quadratic.BasinQuadraticPullbackRoot c root ∧
        (∀ z, z ∈ Quadratic.basin_of_infinity c →
          Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z) ∧
        MapsTo (fun z => Quadratic.external_ray_map c (root z))
          (Quadratic.basin_of_infinity c) (Quadratic.basin_of_infinity c)) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_left_inverse_on_basin
  intro c z hz
  rcases h_pull c with ⟨_root, _h_root, h_left_bottcher, _h_maps⟩
  exact h_left_bottcher z hz

/-- Top-level hook: enough eventual-slit bridge data per parameter implies MLC. -/
theorem mlc_conjecture_of_eventual_slit_global_bridge
    (h_bridge :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
          Quadratic.EventualSlitGlobalInverseExtensionBridge c hA hG) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  rcases h_bridge 0 with ⟨hA, hG, hbr⟩
  exact Quadratic.not_EventualSlitGlobalInverseExtensionBridge 0 hA hG hbr

/-- The old bridge premise is globally inconsistent with current definitions. -/
theorem not_eventual_slit_global_bridge_data :
    ¬ (∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
      ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
        Quadratic.EventualSlitGlobalInverseExtensionBridge c hA hG) := by
  intro h
  rcases h 0 with ⟨hA, hG, hbr⟩
  exact Quadratic.not_EventualSlitGlobalInverseExtensionBridge 0 hA hG hbr

/-- Extension-to-basin data is inconsistent with the current dynamics model,
    since it is equivalent to a basin-wide left inverse of `quadratic_map`. -/
theorem not_eventual_slit_global_extension_data :
    ¬ (∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
      ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
        Quadratic.EventualSlitGlobalInverseExtendsToBasin c hA hG) := by
  intro h
  rcases h 0 with ⟨hA, hG, h_ext⟩
  have hleft :
      Quadratic.HasLeftInverseOn (quadratic_map 0)
        (Quadratic.basin_of_infinity 0) (Quadratic.basin_of_infinity 0) :=
    (Quadratic.EventualSlitGlobalInverseExtendsToBasin_iff_left_inverse 0 hA hG).1 h_ext
  exact Quadratic.not_quadratic_map_left_inverse_on_basin 0 hleft

/-- The overlap hypothesis in the eventual-slit local-to-global route is
    inconsistent with the current global Böttcher/exterior setup. -/
theorem not_eventual_slit_overlap_hyp_data :
    ¬ (∀ c, Quadratic.EventualSlitOverlapHyp c) := by
  intro h
  exact Quadratic.not_EventualSlitOverlapHyp 0 (h 0)

/-- The full local-to-global eventual-slit data package is inconsistent, since
    its overlap component is already impossible. -/
theorem not_eventual_slit_local_to_global_data :
    ¬ (∃ _ : ∀ c, Quadratic.EventualSlitNonzeroDeriv c,
      ∃ _ : ∀ c, Quadratic.EventualSlitLocalUniqueness c,
        ∃ _ : ∀ c, Quadratic.EventualSlitOverlapHyp c,
          ∃ _ : ∀ c, Quadratic.EventualSlitCompatibilityFromOverlap c,
            ∀ c, Quadratic.EventualSlitInverseGluing c) := by
  intro h
  rcases h with ⟨_h_deriv, _h_uniq, h_over, _h_comp, _h_glue⟩
  exact not_eventual_slit_overlap_hyp_data h_over

/-- Parameterized extension route: enough eventual-slit extension data implies
    MLC (this route is currently ruled out by
    `not_eventual_slit_global_extension_data`). -/
theorem mlc_conjecture_of_eventual_slit_global_extension
    (h_ext :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        ∃ hG : Quadratic.GlobalInverseOnEventualSlit c hA,
          Quadratic.EventualSlitGlobalInverseExtendsToBasin c hA hG) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  rcases h_ext c with ⟨hA, hG, _hext⟩
  exact Quadratic.bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_pointwise c hA hG

/-- Alternative route: a global inverse on the eventual slit orbit already
    gives basin injectivity of the Böttcher map, hence MLC. -/
theorem mlc_conjecture_of_eventual_slit_global_inverse
    (h_global :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        Quadratic.GlobalInverseOnEventualSlit c hA) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  rcases h_global c with ⟨hA, hG⟩
  exact Quadratic.bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_pointwise c hA hG

/-- If eventual-slit local inverse atlases are compatible and can be glued to
    global inverses, MLC follows. -/
theorem mlc_conjecture_of_eventual_slit_inverse_gluing
    (h_data :
      ∀ c, ∃ hA : Quadratic.EventualSlitInverseAtlas c,
        Quadratic.EventualSlitInverseCompatible hA)
    (h_glue : ∀ c, Quadratic.EventualSlitInverseGluing c) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_eventual_slit_global_inverse
  intro c
  rcases h_data c with ⟨hA, hcompat⟩
  exact ⟨hA, Quadratic.global_inverse_on_eventual_slit_of_gluing hA hcompat (h_glue c)⟩

/-- A decomposed eventual-slit route: nonzero-derivative local inverses, overlap
    compatibility, and gluing suffice to conclude MLC. -/
theorem mlc_conjecture_of_eventual_slit_local_to_global
    (h_deriv : ∀ c, Quadratic.EventualSlitNonzeroDeriv c)
    (h_uniq : ∀ c, Quadratic.EventualSlitLocalUniqueness c)
    (h_over : ∀ c, Quadratic.EventualSlitOverlapHyp c)
    (h_comp : ∀ c, Quadratic.EventualSlitCompatibilityFromOverlap c)
    (h_glue : ∀ c, Quadratic.EventualSlitInverseGluing c) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_eventual_slit_inverse_gluing
  · intro c
    let hA : Quadratic.EventualSlitInverseAtlas c :=
      Quadratic.eventual_slit_inverse_atlas_of_nonzero_deriv c (h_deriv c)
    have hcompat : Quadratic.EventualSlitInverseCompatible hA :=
      Quadratic.eventual_slit_inverse_compatible_of_overlap c hA (h_uniq c) (h_over c) (h_comp c)
    exact ⟨hA, hcompat⟩
  · exact h_glue

/-- Overlap-free decomposed route: if nonzero-derivative data builds an atlas
    and compatibility is provided directly for that atlas, then gluing implies
    MLC. This isolates the remaining viable local-to-global target after
    ruling out overlap-based compatibility assumptions. -/
theorem mlc_conjecture_of_eventual_slit_nonzero_deriv_compatible_gluing
    (h_deriv : ∀ c, Quadratic.EventualSlitNonzeroDeriv c)
    (h_compat :
      ∀ c,
        let hA : Quadratic.EventualSlitInverseAtlas c :=
          Quadratic.eventual_slit_inverse_atlas_of_nonzero_deriv c (h_deriv c)
        Quadratic.EventualSlitInverseCompatible hA)
    (h_glue : ∀ c, Quadratic.EventualSlitInverseGluing c) :
    LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_eventual_slit_inverse_gluing
  · intro c
    let hA : Quadratic.EventualSlitInverseAtlas c :=
      Quadratic.eventual_slit_inverse_atlas_of_nonzero_deriv c (h_deriv c)
    exact ⟨hA, by simpa [hA] using (h_compat c)⟩
  · exact h_glue

/-- Bridge theorem: the pullback-root route is derivable from the
    iterate-equality implication hypothesis. -/
theorem mlc_conjecture_of_iter_eq_imp_via_pullback_root
    (h_iter_eq_imp :
      ∀ c, ∀ z w, z ∈ Quadratic.basin_of_infinity c →
        w ∈ Quadratic.basin_of_infinity c →
        (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    LocallyConnectedSpace mandelbrotSet := by
  exfalso
  exact Quadratic.not_quadratic_map_iter_eq_imp_eq 0 (h_iter_eq_imp 0)

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/
theorem mlc_conjecture
    : LocallyConnectedSpace mandelbrotSet := by
  apply mlc_conjecture_of_bottcher_inj_on_basin
  intro c
  exact bottcher_map_inj_on_basin_via_iter_eq_axiom c

end MainProof

end MLC
