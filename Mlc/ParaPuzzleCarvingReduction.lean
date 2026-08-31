import Mlc.ParaPuzzleConnectivity
import Mlc.Quadratic.Complex.Bottcher.Slodkowski
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Carving-motion interface around the straddling frontier

The live frontier is the straddling axiom
`MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`, whose
target is

  `IsConnected ({c' | G_c(c'-c) < (1/2)^n} ∩ MandelbrotSet)`.

The translated Green sublevel `{c' | G_c(c'-c) < (1/2)^n}` is already proved
connected (`green_sublevel_translate_connected`), so the residual content is the
intersection with `MandelbrotSet`.

This file keeps a historically motivated carving interface and proves its
fundamental no-go fact on the live straddling stratum:
`not_paraPieceCarvedByMotion_of_straddling`. Thus the carving hypothesis remains
logically meaningful, but it is not a viable reduction for the remaining
frontier.
-/

namespace MLC

open MLC.Quadratic Complex Topology Set Metric

/-- **Attempted carving-motion interface for a single parameter piece.** There is
a space-holomorphic motion of the parameter translate `{c' | G_c(c'-c) < (1/2)^n}`
whose image, at some time in the unit disk, is exactly that translate intersected
with the Mandelbrot set. This remains a logically consistent predicate, but on
the live straddling frontier it is refuted by
`not_paraPieceCarvedByMotion_of_straddling`. Historical Douady–Hubbard
motivation may be kept in mind, but this predicate should not be treated as a
currently viable reduction route. -/
def ParaPieceCarvedByMotion (c : ℂ) (n : ℕ) : Prop :=
  ∃ (H : Quadratic.SpaceHolomorphicMotion
          {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}) (t : ℂ),
    t ∈ Metric.ball (0 : ℂ) 1 ∧
      H.f t '' {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet

/-- **Conditional connectivity from carving.** For `c ∈ M`, if the parameter
translate is carved out by a space-holomorphic motion, then the intersection with
`M` is connected.

This theorem is logically valid, but it is unusable on the live straddling
frontier because `not_paraPieceCarvedByMotion_of_straddling` refutes its
hypothesis exactly there. -/
theorem isConnected_greenSublevel_inter_mandelbrot_of_carvedByMotion
    {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ)
    (h : ParaPieceCarvedByMotion c n) :
    IsConnected ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  obtain ⟨H, t, ht, himg⟩ := h
  rw [← himg]
  exact H.isConnected_image ht (green_sublevel_translate_connected hc n)

private theorem greenSublevel_translate_isOpen (c : ℂ) (n : ℕ) :
    IsOpen {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} := by
  have hcont : Continuous fun c' : ℂ => green_function c (c' - c) :=
    (continuous_green_function c).comp (continuous_id.sub continuous_const)
  simpa using isOpen_lt hcont continuous_const

private theorem spaceHolomorphicMotion_slice_image_isOpen
    {E : Set ℂ} (H : Quadratic.SpaceHolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) 1) (hE_open : IsOpen E) :
    IsOpen (H.f t '' E) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨z, hzE, rfl⟩
  rcases (_root_.mem_nhds_iff.mp (hE_open.mem_nhds hzE)) with ⟨B, hBsubE, hBopen, hzB⟩
  rcases Metric.isOpen_iff.mp hBopen z hzB with ⟨ε, hε, hballsub⟩
  have hwBall : z + (ε / 2 : ℝ) ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hhalf : ‖(ε / 2 : ℝ)‖ < ε := by
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hhalf
  have hB_nonconst : ¬ ∀ᶠ w in 𝓝 z, H.f t w = H.f t z := by
    intro hconst
    have hconstSet : {w : ℂ | H.f t w = H.f t z} ∈ 𝓝 z :=
      Filter.mem_of_superset hconst (by
        intro w hw
        simpa using hw)
    rcases _root_.mem_nhds_iff.mp hconstSet with ⟨s, hsSub, hsOpen, hzs⟩
    rcases Metric.isOpen_iff.mp hsOpen z hzs with ⟨δ, hδ, hδsub⟩
    let r : ℝ := min (ε / 2) (δ / 2)
    have hr_pos : 0 < r := by
      dsimp [r]
      exact lt_min (half_pos hε) (half_pos hδ)
    have hr_lt_δ : r < δ := by
      dsimp [r]
      have hle : r ≤ δ / 2 := min_le_right _ _
      linarith
    have hr_lt_ε : r < ε := by
      dsimp [r]
      have hle : r ≤ ε / 2 := min_le_left _ _
      linarith
    have hsBall : z + (r : ℝ) ∈ Metric.ball z δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hrnorm : ‖r‖ < δ := by
        rw [Real.norm_eq_abs, abs_of_pos hr_pos]
        exact hr_lt_δ
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrnorm
    have hzsmall : z + (r : ℝ) ∈ E := by
      apply hBsubE
      apply hballsub
      rw [Metric.mem_ball, dist_eq_norm]
      have hrnorm : ‖r‖ < ε := by
        rw [Real.norm_eq_abs, abs_of_pos hr_pos]
        exact hr_lt_ε
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hrnorm
    have hsin : z + (r : ℝ) ∈ s := hδsub hsBall
    have hnear : H.f t (z + (r : ℝ)) = H.f t z := hsSub hsin
    have hneq : z + (r : ℝ) ≠ z := by
      have hrne : (r : ℝ) ≠ 0 := by linarith
      exact by simpa using hrne
    exact hneq <| (H.h_inj t ht hzE hzsmall) hnear.symm |>.symm
  have hzU : H.U ∈ 𝓝 z := H.hU_open.mem_nhds (H.hEU hzE)
  have hanalytic : AnalyticAt ℂ (H.f t) z :=
    (H.h_space_holo t ht).analyticAt hzU
  have hmap : 𝓝 (H.f t z) ≤ Filter.map (H.f t) (𝓝 z) :=
    (AnalyticAt.eventually_constant_or_nhds_le_map_nhds hanalytic).resolve_left hB_nonconst
  have hpre : H.f t ⁻¹' (H.f t '' E) ∈ 𝓝 z :=
    Filter.mem_of_superset (hE_open.mem_nhds hzE) (by
      intro u hu
      exact ⟨u, hu, rfl⟩)
  exact hmap hpre

private theorem greenSublevel_translate_inter_mandelbrot_not_open
    {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle : ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
      ⊆ MandelbrotSet)) :
    ¬ IsOpen ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) := by
  let S : Set ℂ := {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
  have hSpre : IsPreconnected S := (green_sublevel_translate_connected hc n).2
  have hcS : c ∈ S := by
    have h0 : green_function c 0 < (1 / 2 : ℝ) ^ n :=
      Quadratic.green_sublevel_contains_0 c n hc
    simpa [S] using h0
  rcases not_subset.1 hstraddle with ⟨x, hxSraw, hxM⟩
  have hxS : x ∈ S := by simpa [S] using hxSraw
  intro hOpen
  have hu : IsOpen (S ∩ MandelbrotSet) := by simpa [S] using hOpen
  have hv : IsOpen (S ∩ MandelbrotSetᶜ) := by
    simpa [S] using (greenSublevel_translate_isOpen c n).inter isOpen_compl_mandelbrotSet
  have huv : Disjoint (S ∩ MandelbrotSet) (S ∩ MandelbrotSetᶜ) := by
    refine disjoint_left.2 ?_
    intro z hzU hzV
    exact hzV.2 hzU.2
  have hSuv : S ⊆ (S ∩ MandelbrotSet) ∪ (S ∩ MandelbrotSetᶜ) := by
    intro z hzS
    by_cases hzM : z ∈ MandelbrotSet
    · exact Or.inl ⟨hzS, hzM⟩
    · exact Or.inr ⟨hzS, hzM⟩
  have hsu : (S ∩ (S ∩ MandelbrotSet)).Nonempty := by
    refine ⟨c, ?_⟩
    exact ⟨hcS, hcS, hc⟩
  have hsubset : S ⊆ S ∩ MandelbrotSet :=
    hSpre.subset_left_of_subset_union hu hv huv hSuv hsu
  have hxu : x ∈ S ∩ MandelbrotSet := hsubset hxS
  exact hxM hxu.2

/-- A straddling Green-sublevel translate cannot be carved out as the exact image
of a space-holomorphic motion slice: the slice image is open, while the target
intersection with `MandelbrotSet` is not. -/
theorem not_paraPieceCarvedByMotion_of_straddling
    {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle : ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
      ⊆ MandelbrotSet)) :
    ¬ ParaPieceCarvedByMotion c n := by
  intro hcarved
  obtain ⟨H, t, ht, himg⟩ := hcarved
  have hOpenImg : IsOpen (H.f t '' {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}) :=
    spaceHolomorphicMotion_slice_image_isOpen H ht (greenSublevel_translate_isOpen c n)
  have hNotOpen :
      ¬ IsOpen ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet) :=
    greenSublevel_translate_inter_mandelbrot_not_open hc n hstraddle
  exact hNotOpen <| himg ▸ hOpenImg

end MLC
