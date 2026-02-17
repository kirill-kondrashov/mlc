import Mlc.Quadratic.Complex.Bottcher.BottcherAxioms
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace MLC

open Quadratic Complex Topology Set Filter Metric

namespace Quadratic

/-!
Sketch: continuity of the external ray map on the exterior of the unit disk.

Idea: if `bottcher_map c` is a continuous, injective, open map onto an open set,
then it is an open embedding. Its inverse (as an open partial homeomorphism)
is continuous on the target, and it agrees with `external_ray_map c` on
`{w | 1 < ‖w‖}`. Replace the axioms below with the needed hypotheses.
-/

lemma ray_map_eq_on_symm
    (c : ℂ)
    (h_emb : IsOpenEmbedding (bottcher_map c))
    (h_surj : {w : ℂ | 1 < ‖w‖} ⊆ Set.range (bottcher_map c)) :
    Set.EqOn (external_ray_map c)
      (h_emb.toOpenPartialHomeomorph (bottcher_map c)).symm {w : ℂ | 1 < ‖w‖} := by
  intro w hw
  have hw' : w ∈ Set.range (bottcher_map c) := h_surj hw
  rcases hw' with ⟨a, rfl⟩
  have h_inv :
      bottcher_map c (external_ray_map c (bottcher_map c a)) =
        bottcher_map c a := by
    have hw' : 1 < ‖bottcher_map c a‖ := by
      simpa using hw
    simpa using external_ray_map_right_inverse c (bottcher_map c a) hw'
  have h_symm :
      bottcher_map c
        ((h_emb.toOpenPartialHomeomorph (bottcher_map c)).symm (bottcher_map c a)) =
          bottcher_map c a := by
    simpa using
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv (f := bottcher_map c)
        (h := h_emb) (x := bottcher_map c a) ⟨a, rfl⟩)
  have h_eq :
      external_ray_map c (bottcher_map c a) =
        (h_emb.toOpenPartialHomeomorph (bottcher_map c)).symm (bottcher_map c a) := by
    have hpre :
        bottcher_map c (external_ray_map c (bottcher_map c a)) =
          bottcher_map c
            ((h_emb.toOpenPartialHomeomorph (bottcher_map c)).symm (bottcher_map c a)) := by
      calc
        bottcher_map c (external_ray_map c (bottcher_map c a)) = bottcher_map c a := h_inv
        _ = bottcher_map c
              ((h_emb.toOpenPartialHomeomorph (bottcher_map c)).symm (bottcher_map c a)) := by
              simpa using h_symm.symm
    exact h_emb.injective hpre
  simpa using h_eq

lemma ray_map_target_subset
    (c : ℂ)
    (h_emb : IsOpenEmbedding (bottcher_map c))
    (h_surj : {w : ℂ | 1 < ‖w‖} ⊆ Set.range (bottcher_map c)) :
    {w : ℂ | 1 < ‖w‖} ⊆
      (h_emb.toOpenPartialHomeomorph (bottcher_map c)).target := by
  intro w hw
  have hw' : w ∈ Set.range (bottcher_map c) := h_surj hw
  simpa using
    (show w ∈ (h_emb.toOpenPartialHomeomorph (bottcher_map c)).target from
      by simpa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] using hw')

theorem ray_map_continuous_on
    (c : ℂ)
    (h_cont : Continuous (bottcher_map c))
    (h_inj : Function.Injective (bottcher_map c))
    (h_open : IsOpenMap (bottcher_map c))
    (h_surj : {w : ℂ | 1 < ‖w‖} ⊆ Set.range (bottcher_map c)) :
    ContinuousOn (external_ray_map c) {w | 1 < ‖w‖} := by
  -- 1) Promote `bottcher_map c` to an open embedding.
  have h_emb : IsOpenEmbedding (bottcher_map c) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap h_cont h_inj h_open

  -- 2) Let `e` be the associated open partial homeomorphism.
  let e := h_emb.toOpenPartialHomeomorph (bottcher_map c)

  -- 3) Show `external_ray_map c` agrees with `e.symm` on `{w | 1 < ‖w‖}`.
  have h_eq_on :
      Set.EqOn (external_ray_map c) e.symm {w : ℂ | 1 < ‖w‖} := by
    -- Use `ray_map_eq_on_symm` to relate `external_ray_map` and `e.symm`.
    simpa [e] using ray_map_eq_on_symm (c := c) h_emb h_surj

  -- 4) Show `{w | 1 < ‖w‖} ⊆ e.target`.
  have h_subset : {w : ℂ | 1 < ‖w‖} ⊆ e.target := by
    -- Use `ray_map_target_subset` to show the exterior lies in `e.target`.
    simpa [e] using ray_map_target_subset (c := c) h_emb h_surj

  -- 5) Conclude continuity of `external_ray_map` on the exterior.
  exact (e.continuousOn_symm.congr_mono h_eq_on h_subset)

theorem external_ray_map_continuousOn_exterior_of_inj_open
    (c : ℂ)
    (h_cont : Continuous (bottcher_map c))
    (h_inj : Function.Injective (bottcher_map c))
    (h_open : IsOpenMap (bottcher_map c)) :
    ContinuousOn (external_ray_map c) {w | 1 < ‖w‖} := by
  have h_surj : {w : ℂ | 1 < ‖w‖} ⊆ Set.range (bottcher_map c) := by
    intro w hw
    rcases (bottcher_map_surj c w hw) with ⟨a, _ha, rfl⟩
    exact ⟨a, rfl⟩
  exact ray_map_continuous_on c h_cont h_inj h_open h_surj

end Quadratic

end MLC
