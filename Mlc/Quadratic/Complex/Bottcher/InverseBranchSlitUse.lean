import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.InverseBranchSlit

namespace MLC
namespace Quadratic

open Topology Filter

lemma bottcher_left_inverse_on_slit_orbit_of_global_inverse
    (c : ℂ) (hA : SlitInverseAtlas c) (hG : GlobalInverseOnSlit c hA) :
    ∀ z, z ∈ slit_orbit c ∩ basin_of_infinity c →
      ∀ᶠ x in 𝓝 z, (Classical.choose hG) (bottcher_map c x) = x := by
  intro z hz
  simpa using (global_inverse_left_inverse_on_slit (c := c) (hA := hA) hG z hz)

lemma bottcher_left_inverse_on_eventual_slit_of_global_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
      ∀ᶠ x in 𝓝 z, (Classical.choose hG) (bottcher_map c x) = x := by
  have hleft := (Classical.choose_spec hG).2
  intro z hz
  simpa using (hleft z hz)

theorem bottcher_map_inj_on_basin_of_eventual_slit_global_inverse
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.bottcher_map c z) ^ (2 ^ n))
    (hA : EventualSlitInverseAtlas c)
    (hG : GlobalInverseOnEventualSlit c hA)
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) := by
  -- This lemma mirrors `bottcher_map_inj_on_basin_of_outside_left_inv` but
  -- highlights the eventual-slit global inverse as a potential source for
  -- a left-inverse on the basin.
  exact bottcher_map_inj_on_basin_of_outside_left_inv c h_left h_escape h_conj h_iter_eq_imp

theorem bottcher_map_inj_theorem_of_eventual_slit_global_inverse
    (c : ℂ)
    (h_left : ∀ z, z ∈ outside_disk c →
      Quadratic.external_ray_map c (Quadratic.bottcher_map c z) = z)
    (h_escape : ∀ z, z ∈ Quadratic.basin_of_infinity c →
      ∃ n, (quadratic_map c)^[n] z ∈ outside_disk c)
    (h_conj : ∀ n z, z ∈ Quadratic.basin_of_infinity c →
      Quadratic.bottcher_map c ((quadratic_map c)^[n] z) =
        (Quadratic.bottcher_map c z) ^ (2 ^ n))
    (h_inj_K : Set.InjOn (Quadratic.bottcher_map c) (MLC.Quadratic.K c))
    (hA : EventualSlitInverseAtlas c)
    (hG : GlobalInverseOnEventualSlit c hA)
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Function.Injective (Quadratic.bottcher_map c) := by
  have h_inj_basin :
      Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) :=
    bottcher_map_inj_on_basin_of_eventual_slit_global_inverse c h_left h_escape h_conj hA hG
      h_iter_eq_imp
  have h_pre : ∀ z, 1 < ‖Quadratic.bottcher_map c z‖ →
      z ∈ Quadratic.basin_of_infinity c := by
    intro z hz
    have hnorm' : ‖Quadratic.bottcher_map c z‖ =
        Real.exp (MLC.Quadratic.green_function c z) :=
      Quadratic.norm_bottcher_eq_exp_green c z
    have hpos : 0 < MLC.Quadratic.green_function c z := by
      have hgt : 1 < Real.exp (MLC.Quadratic.green_function c z) := by
        simpa [hnorm'] using hz
      exact (Real.one_lt_exp_iff).1 hgt
    have hz' : z ∉ MLC.Quadratic.K c :=
      (MLC.Quadratic.green_function_pos_iff_not_mem_K c z).1 hpos
    have : z ∈ (MLC.Quadratic.K c)ᶜ := by
      simpa [Set.mem_compl_iff] using hz'
    simpa [Quadratic.basin_eq_compl_K c] using this
  have h_inj_on :
      Set.InjOn (Quadratic.bottcher_map c) {z | 1 < ‖Quadratic.bottcher_map c z‖} :=
    bottcher_map_injective_of_basin_characterization (c := c) h_pre h_inj_basin
  intro z w hzw
  by_cases hz : 1 < ‖Quadratic.bottcher_map c z‖
  · have hw : 1 < ‖Quadratic.bottcher_map c w‖ := by
      simpa [hzw] using hz
    exact h_inj_on hz hw hzw
  · have hz_le : ‖Quadratic.bottcher_map c z‖ ≤ 1 := le_of_not_gt hz
    have hnorm' : ‖Quadratic.bottcher_map c z‖ =
        Real.exp (MLC.Quadratic.green_function c z) :=
      Quadratic.norm_bottcher_eq_exp_green c z
    have hge0 : 0 ≤ MLC.Quadratic.green_function c z :=
      MLC.Quadratic.green_function_nonneg c z
    have hle0 : MLC.Quadratic.green_function c z ≤ 0 := by
      have : Real.exp (MLC.Quadratic.green_function c z) ≤ 1 := by
        simpa [hnorm'] using hz_le
      exact (Real.exp_le_one_iff).1 this
    have hzG : MLC.Quadratic.green_function c z = 0 := le_antisymm hle0 hge0
    have hzK : z ∈ MLC.Quadratic.K c :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K c z).1 hzG
    have hnormw : ‖Quadratic.bottcher_map c w‖ ≤ 1 := by
      simpa [hzw] using hz_le
    have hnormw' : ‖Quadratic.bottcher_map c w‖ =
        Real.exp (MLC.Quadratic.green_function c w) :=
      Quadratic.norm_bottcher_eq_exp_green c w
    have hge0w : 0 ≤ MLC.Quadratic.green_function c w :=
      MLC.Quadratic.green_function_nonneg c w
    have hle0w : MLC.Quadratic.green_function c w ≤ 0 := by
      have : Real.exp (MLC.Quadratic.green_function c w) ≤ 1 := by
        simpa [hnormw'] using hnormw
      exact (Real.exp_le_one_iff).1 this
    have hwG : MLC.Quadratic.green_function c w = 0 := le_antisymm hle0w hge0w
    have hwK : w ∈ MLC.Quadratic.K c :=
      (MLC.Quadratic.green_function_eq_zero_iff_mem_K c w).1 hwG
    exact h_inj_K hzK hwK hzw

/-!
Step 2: extension bridge to a left inverse for all iterates on the basin.

This is a hypothesis-only interface that captures the remaining gap.
-/

def EventualSlitGlobalInverseExtendsToBasinIter (c : ℂ) : Prop :=
  ∀ n : ℕ, HasLeftInverseOn ((quadratic_map c)^[n]) (basin_of_infinity c) (basin_of_infinity c)

def BasinEventuallyInEventualSlit (c : ℂ) : Prop :=
  ∀ z, z ∈ basin_of_infinity c → ∃ N, (quadratic_map c)^[N] z ∈ eventual_slit_set c

def OrbitInverseBranchSystem (c : ℂ) : Prop :=
  ∀ n : ℕ, ∃ g : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → g ((quadratic_map c)^[n] z) = z) ∧
    (∀ z, z ∈ basin_of_infinity c → g z ∈ basin_of_infinity c)

def EventualSlitGlobalInverseExtensionHyp (c : ℂ) : Prop :=
  BasinEventuallyInEventualSlit c ∧ OrbitInverseBranchSystem c

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp
    (c : ℂ) (h_ext : EventualSlitGlobalInverseExtensionHyp c) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  intro n
  rcases h_ext.2 n with ⟨g, hleft, hmap⟩
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact hleft z hz
  · intro z hz
    exact hmap z hz

def EventualSlitGlobalInverseExtensionToIter (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) : Prop :=
  EventualSlitGlobalInverseExtendsToBasinIter c

lemma quadratic_map_iter_eq_imp_eq_of_extension_iter
    (c : ℂ) (hiter : EventualSlitGlobalInverseExtendsToBasinIter c) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  intro z w hz hw hiter_eq
  have h_inj : ∀ n, Set.InjOn ((quadratic_map c)^[n]) (basin_of_infinity c) := by
    intro n
    exact injOn_of_hasLeftInverseOn (hiter n)
  exact quadratic_map_iter_eq_imp_eq_of_all_iter_inj c h_inj z w hz hw hiter_eq

lemma quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_extension
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtensionToIter c hA hG) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  exact quadratic_map_iter_eq_imp_eq_of_extension_iter c h_ext

lemma quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_extension_hyp
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtensionHyp c) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hiter := EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext
  exact quadratic_map_iter_eq_imp_eq_of_extension_iter c hiter

/-!
Step 2 scaffolding: extend the eventual-slit global inverse to the full basin.
This is the precise missing bridge needed to derive a left inverse for
`quadratic_map` on the basin and eliminate `quadratic_map_iter_eq_imp_eq`.
-/

def EventualSlitGlobalInverseExtendsToBasin (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) : Prop :=
  ∃ g : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → g (quadratic_map c z) = z) ∧
    (∀ z, z ∈ basin_of_infinity c → g z ∈ basin_of_infinity c)

lemma quadratic_map_left_inverse_on_basin_of_global_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtendsToBasin c hA hG) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  rcases h_ext with ⟨g, hleft, hmap⟩
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact hleft z hz
  · intro z hz
    exact hmap z hz

end Quadratic
end MLC
