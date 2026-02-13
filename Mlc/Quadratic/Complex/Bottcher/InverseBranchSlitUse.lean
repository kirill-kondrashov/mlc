import Mlc.Quadratic.Complex.Bottcher.BottcherOnMTheory
import Mlc.Quadratic.Complex.Bottcher.BottcherOutsidePlan
import Mlc.Quadratic.Complex.Bottcher.InverseBranchSlit

namespace MLC
namespace Quadratic

open Topology Filter Set

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

lemma bottcher_left_inverse_pointwise_on_eventual_slit_of_global_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
      (Classical.choose hG) (bottcher_map c z) = z := by
  intro z hz
  have h := bottcher_left_inverse_on_eventual_slit_of_global_inverse c hA hG z hz
  refine (Filter.Eventually.self_of_nhds
    (p := fun x => (Classical.choose hG) (bottcher_map c x) = x) h)

/-- Redesigned Step 2b target at a fixed parameter: a pointwise left-inverse
    identity for `bottcher_map` on the eventual-slit basin set. -/
def EventualSlitPointwiseLeftInverseData (c : ℂ) : Prop :=
  ∃ g : ℂ → ℂ,
    ∀ z, z ∈ eventual_slit_set c ∩ basin_of_infinity c →
      g (bottcher_map c z) = z

/-- Minimal basin target corresponding to Step 2b: a pointwise left-inverse
    identity for `bottcher_map` on the whole basin. -/
def BasinBottcherPointwiseLeftInverseData (c : ℂ) : Prop :=
  ∃ g : ℂ → ℂ,
    ∀ z, z ∈ basin_of_infinity c →
      g (bottcher_map c z) = z

lemma eventual_slit_pointwise_left_inverse_data_of_global_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    EventualSlitPointwiseLeftInverseData c := by
  refine ⟨Classical.choose hG, ?_⟩
  intro z hz
  exact bottcher_left_inverse_pointwise_on_eventual_slit_of_global_inverse c hA hG z hz

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
    (_hG : GlobalInverseOnEventualSlit c hA)
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
    (_hG : GlobalInverseOnEventualSlit c hA)
    (h_iter_eq_imp : ∀ z w, z ∈ Quadratic.basin_of_infinity c → w ∈ Quadratic.basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    Function.Injective (Quadratic.bottcher_map c) := by
  have h_inj_basin :
      Set.InjOn (Quadratic.bottcher_map c) (Quadratic.basin_of_infinity c) :=
    bottcher_map_inj_on_basin_of_eventual_slit_global_inverse c h_left h_escape h_conj hA _hG
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

lemma eventual_slit_orbit_of_iter_eventual
    (c z : ℂ) (N : ℕ)
    (hN : (quadratic_map c)^[N] z ∈ eventual_slit_set c) :
    z ∈ eventual_slit_set c := by
  rcases hN with ⟨M, hM⟩
  refine ⟨M + N, ?_⟩
  intro n hn
  have hNn : N ≤ n := by
    exact le_trans (Nat.le_add_left N M) hn
  have hsub : M ≤ n - N := by
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn)
  have hslit :
      (quadratic_map c)^[n - N] ((quadratic_map c)^[N] z) ∈ Complex.slitPlane :=
    hM (n - N) hsub
  have hrewrite :
      (quadratic_map c)^[n] z =
        (quadratic_map c)^[n - N] ((quadratic_map c)^[N] z) := by
    calc
      (quadratic_map c)^[n] z = (quadratic_map c)^[n - N + N] z := by
        simp [Nat.sub_add_cancel hNn]
      _ = (quadratic_map c)^[n - N] ((quadratic_map c)^[N] z) := by
        simp [Function.iterate_add, Function.comp_apply]
  simpa [hrewrite] using hslit

lemma basin_eventually_in_eventual_slit (c : ℂ) :
    BasinEventuallyInEventualSlit c := by
  intro z hz
  rcases basin_escape_outside_open c z hz with ⟨n0, hn0⟩
  have h_eventual := outside_eventually_slit_orbit c ((quadratic_map c)^[n0] z) hn0
  rcases h_eventual with ⟨N, hN⟩
  refine ⟨N + n0, ?_⟩
  change eventually_slit_orbit c ((quadratic_map c)^[N + n0] z)
  refine ⟨0, ?_⟩
  intro m hm
  have hslit :
      (quadratic_map c)^[m + N] ((quadratic_map c)^[n0] z) ∈ Complex.slitPlane :=
    hN (m + N) (Nat.le_add_left _ _)
  have hrewrite :
      (quadratic_map c)^[m] ((quadratic_map c)^[N + n0] z) =
        (quadratic_map c)^[m + N] ((quadratic_map c)^[n0] z) := by
    simp [Function.iterate_add, Function.comp_apply]
  simpa [hrewrite] using hslit

lemma basin_subset_eventual_slit_set (c : ℂ) :
    basin_of_infinity c ⊆ eventual_slit_set c := by
  intro z hz
  rcases basin_eventually_in_eventual_slit c z hz with ⟨N, hN⟩
  exact eventual_slit_orbit_of_iter_eventual c z N hN

lemma basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_data
    (c : ℂ) (h_data : EventualSlitPointwiseLeftInverseData c) :
    BasinBottcherPointwiseLeftInverseData c := by
  refine ⟨Classical.choose h_data, ?_⟩
  intro z hz
  have hz_eventual : z ∈ eventual_slit_set c := basin_subset_eventual_slit_set c hz
  exact (Classical.choose_spec h_data) z ⟨hz_eventual, hz⟩

lemma eventual_slit_pointwise_left_inverse_data_of_basin_bottcher_data
    (c : ℂ) (h_data : BasinBottcherPointwiseLeftInverseData c) :
    EventualSlitPointwiseLeftInverseData c := by
  refine ⟨Classical.choose h_data, ?_⟩
  intro z hz
  exact (Classical.choose_spec h_data) z hz.2

lemma eventual_slit_pointwise_left_inverse_data_iff_basin_bottcher_pointwise_left_inverse_data
    (c : ℂ) :
    EventualSlitPointwiseLeftInverseData c ↔ BasinBottcherPointwiseLeftInverseData c := by
  constructor
  · exact basin_bottcher_pointwise_left_inverse_data_of_eventual_slit_data c
  · exact eventual_slit_pointwise_left_inverse_data_of_basin_bottcher_data c

lemma bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_global_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    ∀ z, z ∈ basin_of_infinity c → (Classical.choose hG) (bottcher_map c z) = z := by
  intro z hz
  have hz_eventual : z ∈ eventual_slit_set c := basin_subset_eventual_slit_set c hz
  exact bottcher_left_inverse_pointwise_on_eventual_slit_of_global_inverse c hA hG z
    ⟨hz_eventual, hz⟩

lemma bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_data
    (c : ℂ) (h_data : EventualSlitPointwiseLeftInverseData c) :
    ∀ z, z ∈ basin_of_infinity c → (Classical.choose h_data) (bottcher_map c z) = z := by
  intro z hz
  have hz_eventual : z ∈ eventual_slit_set c := basin_subset_eventual_slit_set c hz
  exact (Classical.choose_spec h_data) z ⟨hz_eventual, hz⟩

lemma bottcher_left_inverse_pointwise_on_basin_of_basin_bottcher_data
    (c : ℂ) (h_data : BasinBottcherPointwiseLeftInverseData c) :
    ∀ z, z ∈ basin_of_infinity c → (Classical.choose h_data) (bottcher_map c z) = z := by
  intro z hz
  exact (Classical.choose_spec h_data) z hz

lemma bottcher_map_inj_on_basin_of_eventual_slit_global_inverse_pointwise
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    Set.InjOn (bottcher_map c) (basin_of_infinity c) := by
  intro z hz w hw hzw
  have hzleft :
      (Classical.choose hG) (bottcher_map c z) = z :=
    bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_global_inverse c hA hG z hz
  have hwleft :
      (Classical.choose hG) (bottcher_map c w) = w :=
    bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_global_inverse c hA hG w hw
  have h := congrArg (Classical.choose hG) hzw
  simpa [hzleft, hwleft] using h

lemma bottcher_map_inj_on_basin_of_eventual_slit_pointwise_left_inverse_data
    (c : ℂ) (h_data : EventualSlitPointwiseLeftInverseData c) :
    Set.InjOn (bottcher_map c) (basin_of_infinity c) := by
  intro z hz w hw hzw
  have hzleft :
      (Classical.choose h_data) (bottcher_map c z) = z :=
    bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_data c h_data z hz
  have hwleft :
      (Classical.choose h_data) (bottcher_map c w) = w :=
    bottcher_left_inverse_pointwise_on_basin_of_eventual_slit_data c h_data w hw
  have h := congrArg (Classical.choose h_data) hzw
  simpa [hzleft, hwleft] using h

lemma bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data
    (c : ℂ) (h_data : BasinBottcherPointwiseLeftInverseData c) :
    Set.InjOn (bottcher_map c) (basin_of_infinity c) := by
  intro z hz w hw hzw
  have hzleft :
      (Classical.choose h_data) (bottcher_map c z) = z :=
    bottcher_left_inverse_pointwise_on_basin_of_basin_bottcher_data c h_data z hz
  have hwleft :
      (Classical.choose h_data) (bottcher_map c w) = w :=
    bottcher_left_inverse_pointwise_on_basin_of_basin_bottcher_data c h_data w hw
  have h := congrArg (Classical.choose h_data) hzw
  simpa [hzleft, hwleft] using h


lemma basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin
    (c : ℂ) (h_inj_basin : Set.InjOn (bottcher_map c) (basin_of_infinity c)) :
    BasinBottcherPointwiseLeftInverseData c := by
  refine ⟨external_ray_map c, ?_⟩
  intro z hz
  have hpos : 0 < MLC.Quadratic.green_function c z :=
    green_function_pos_of_basin c z hz
  have hnorm : 1 < ‖bottcher_map c z‖ :=
    bottcher_map_norm_gt_one_of_basin c z hz hpos
  have hright :
      bottcher_map c (external_ray_map c (bottcher_map c z)) = bottcher_map c z :=
    external_ray_map_right_inverse_on_exterior c (bottcher_map c z) hnorm
  have hmem :
      external_ray_map c (bottcher_map c z) ∈ basin_of_infinity c := by
    refine bottcher_map_norm_gt_one_implies_basin c ?_
    simpa [hright] using hnorm
  exact external_ray_map_left_inverse_of_injOn c (s := basin_of_infinity c)
    h_inj_basin hmem hz hnorm

lemma basin_bottcher_pointwise_left_inverse_data_iff_bottcher_map_inj_on_basin
    (c : ℂ) :
    BasinBottcherPointwiseLeftInverseData c ↔
      Set.InjOn (bottcher_map c) (basin_of_infinity c) := by
  constructor
  · intro h_data
    exact bottcher_map_inj_on_basin_of_basin_bottcher_pointwise_left_inverse_data c h_data
  · intro h_inj_basin
    exact basin_bottcher_pointwise_left_inverse_data_of_bottcher_map_inj_on_basin c h_inj_basin
lemma not_EventualSlitOverlapHyp (c : ℂ) :
    ¬ EventualSlitOverlapHyp c := by
  intro h_over
  have hw2 : 1 < ‖(2 : ℂ)‖ := by norm_num
  have hw3 : 1 < ‖(3 : ℂ)‖ := by norm_num
  rcases bottcher_map_surj c (2 : ℂ) hw2 with ⟨z2, _hz2dom, hz2eq⟩
  rcases bottcher_map_surj c (3 : ℂ) hw3 with ⟨z3, _hz3dom, hz3eq⟩
  have hz2norm : 1 < ‖bottcher_map c z2‖ := by
    rw [hz2eq]
    exact hw2
  have hz3norm : 1 < ‖bottcher_map c z3‖ := by
    rw [hz3eq]
    exact hw3
  have hz2_basin : z2 ∈ basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := z2) hz2norm
  have hz3_basin : z3 ∈ basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := z3) hz3norm
  have hz2_eventual : z2 ∈ eventual_slit_set c := basin_subset_eventual_slit_set c hz2_basin
  have hz3_eventual : z3 ∈ eventual_slit_set c := basin_subset_eventual_slit_set c hz3_basin
  have h_nebot :
      Filter.NeBot (𝓝 (bottcher_map c z2) ⊓ 𝓝 (bottcher_map c z3)) :=
    h_over z2 z3 ⟨hz2_eventual, hz2_basin⟩ ⟨hz3_eventual, hz3_basin⟩
  have hphi_eq : bottcher_map c z2 = bottcher_map c z3 := eq_of_nhds_neBot h_nebot
  have h23 : (2 : ℂ) = (3 : ℂ) := by
    rw [hz2eq, hz3eq] at hphi_eq
    exact hphi_eq
  norm_num at h23

lemma eventual_slit_subset_slit_orbit_of_inverse_atlas
    (c : ℂ) (hA : EventualSlitInverseAtlas c) :
    eventual_slit_set c ∩ basin_of_infinity c ⊆ slit_orbit c := by
  intro z hz
  rcases hA z hz with ⟨hLocal, _⟩
  exact hLocal.hUslit hLocal.hz

lemma not_EventualSlitInverseAtlas_zero :
    ¬ EventualSlitInverseAtlas (0 : ℂ) := by
  intro hA
  have hz_large : ‖(-3 : ℂ)‖ > ‖(0 : ℂ)‖ + 2 := by norm_num
  have hz_eventual : (-3 : ℂ) ∈ eventual_slit_set (0 : ℂ) :=
    outside_eventually_slit_orbit 0 (-3 : ℂ) hz_large
  have hz_outside : (-3 : ℂ) ∈ outside_disk (0 : ℂ) :=
    large_norm_mem_outside_disk 0 (-3 : ℂ) (le_of_lt hz_large)
  have hz_basin : (-3 : ℂ) ∈ basin_of_infinity (0 : ℂ) :=
    outside_disk_subset_quadratic_basin 0 hz_outside
  have hz_slit_orbit : (-3 : ℂ) ∈ slit_orbit (0 : ℂ) :=
    eventual_slit_subset_slit_orbit_of_inverse_atlas (0 : ℂ) hA ⟨hz_eventual, hz_basin⟩
  have hz_slit : (-3 : ℂ) ∈ Complex.slitPlane := hz_slit_orbit 0
  have hz_not_slit : (-3 : ℂ) ∉ Complex.slitPlane := by
    intro hslit
    have harg : Complex.arg (-3 : ℂ) = Real.pi := by
      have hneg : (-3 : ℝ) < 0 := by norm_num
      simpa using (Complex.arg_ofReal_of_neg hneg)
    exact (Complex.mem_slitPlane_iff_arg.mp hslit).1 harg
  exact hz_not_slit hz_slit

def OrbitInverseBranchSystem (c : ℂ) : Prop :=
  ∀ n : ℕ, ∃ g : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → g ((quadratic_map c)^[n] z) = z) ∧
    (∀ z, z ∈ basin_of_infinity c → g z ∈ basin_of_infinity c)

def EventualSlitGlobalInverseExtensionHyp (c : ℂ) : Prop :=
  BasinEventuallyInEventualSlit c ∧ OrbitInverseBranchSystem c

lemma eventual_slit_global_inverse_extension_hyp_of_orbit_system
    (c : ℂ) (h_orbit : OrbitInverseBranchSystem c) :
    EventualSlitGlobalInverseExtensionHyp c := by
  exact ⟨basin_eventually_in_eventual_slit c, h_orbit⟩

lemma orbit_inverse_branch_system_of_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    OrbitInverseBranchSystem c := by
  rcases hleft with ⟨g, hleft, hmap⟩
  have hmap' : MapsTo g (basin_of_infinity c) (basin_of_infinity c) := by
    intro z hz
    exact hmap z hz
  have hfmap :
      MapsTo (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    basin_of_infinity_forward_invariant c
  have hfiter :
      ∀ n, MapsTo (quadratic_map c)^[n] (basin_of_infinity c) (basin_of_infinity c) :=
    MapsTo.iterate hfmap
  intro n
  refine ⟨g^[n], ?_, ?_⟩
  · intro z hz
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hz' : (quadratic_map c)^[n] z ∈ basin_of_infinity c :=
          (hfiter n) hz
        have hstep :
            g ((quadratic_map c)^[n + 1] z) = (quadratic_map c)^[n] z := by
          simpa [Function.iterate_succ_apply'] using hleft ((quadratic_map c)^[n] z) hz'
        have hstep' :
            g ((quadratic_map c)^[n] (quadratic_map c z)) = (quadratic_map c)^[n] z := by
          simpa [Function.iterate_succ_apply] using hstep
        have hgsucc :
            (g^[n + 1]) ((quadratic_map c)^[n + 1] z) =
              (g^[n]) (g ((quadratic_map c)^[n + 1] z)) := by
          exact
            (Function.iterate_succ_apply (f := g) (n := n)
              (x := (quadratic_map c)^[n + 1] z))
        calc
          (g^[n + 1]) ((quadratic_map c)^[n + 1] z)
              = (g^[n]) (g ((quadratic_map c)^[n + 1] z)) := hgsucc
          _ = (g^[n]) ((quadratic_map c)^[n] z) := by
                  simp [hstep']
          _ = z := ih
  · intro z hz
    exact (MapsTo.iterate hmap' n) hz

lemma EventualSlitGlobalInverseExtensionHyp_of_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtensionHyp c := by
  exact eventual_slit_global_inverse_extension_hyp_of_orbit_system c
    (orbit_inverse_branch_system_of_left_inverse c hleft)

lemma orbit_inverse_branch_system_of_iter_left_inverse
    (c : ℂ) (hiter : EventualSlitGlobalInverseExtendsToBasinIter c) :
    OrbitInverseBranchSystem c := by
  intro n
  rcases hiter n with ⟨g, hleft, hmap⟩
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact hleft z hz
  · intro z hz
    exact hmap z hz

lemma iter_left_inverse_of_orbit_inverse_branch_system
    (c : ℂ) (h_orbit : OrbitInverseBranchSystem c) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  intro n
  rcases h_orbit n with ⟨g, hleft, hmap⟩
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact hleft z hz
  · intro z hz
    exact hmap z hz

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

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  exact iter_left_inverse_of_orbit_inverse_branch_system c
    (orbit_inverse_branch_system_of_left_inverse c hleft)

def EventualSlitGlobalInverseExtensionToIter (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA) : Prop :=
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

lemma quadratic_map_iter_eq_imp_eq_of_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hiter :
      EventualSlitGlobalInverseExtendsToBasinIter c :=
    EventualSlitGlobalInverseExtendsToBasinIter_of_left_inverse c hleft
  exact quadratic_map_iter_eq_imp_eq_of_extension_iter c hiter

lemma quadratic_map_left_inverse_on_basin_of_iter_eq_imp
    (c : ℂ)
    (h_iter_eq_imp : ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  have h_inj : Set.InjOn (quadratic_map c) (basin_of_infinity c) := by
    intro z hz w hw hzw
    refine h_iter_eq_imp z w hz hw ?_
    exact ⟨1, by simpa using hzw⟩
  have h_nonempty : (basin_of_infinity c).Nonempty := by
    rcases basin_of_infinity_nonempty c with ⟨z, hz⟩
    exact ⟨z, hz⟩
  exact hasLeftInverseOn_of_injOn (S := basin_of_infinity c) h_nonempty h_inj

lemma quadratic_map_not_injOn_basin (c : ℂ) :
    ¬ Set.InjOn (quadratic_map c) (basin_of_infinity c) := by
  let z : ℂ := ((‖c‖ + 3 : ℝ) : ℂ)
  have hz_norm : ‖z‖ = ‖c‖ + 3 := by
    have hnonneg : 0 ≤ ‖c‖ + 3 := by nlinarith [norm_nonneg c]
    simpa [z] using (Complex.norm_of_nonneg hnonneg)
  have hz_large : ‖z‖ > ‖c‖ + 2 := by
    linarith [hz_norm]
  have hz_basin : z ∈ basin_of_infinity c :=
    open_large_ball_subset_basin c hz_large
  have hnegz_large : ‖-z‖ > ‖c‖ + 2 := by
    simpa [norm_neg] using hz_large
  have hnegz_basin : -z ∈ basin_of_infinity c :=
    open_large_ball_subset_basin c hnegz_large
  have hz_ne_negz : z ≠ -z := by
    have hz_ne_zero : z ≠ 0 := by
      intro hz0
      have hz_norm_zero : ‖z‖ = 0 := by simp [hz0]
      have hpos : 0 < ‖z‖ := by
        rw [hz_norm]
        linarith [norm_nonneg c]
      have : (0 : ℝ) < 0 := by
        calc
          (0 : ℝ) < ‖z‖ := hpos
          _ = 0 := hz_norm_zero
      exact (lt_irrefl (0 : ℝ)) this
    intro h
    have hmul : (2 : ℂ) * z = 0 := by
      calc
        (2 : ℂ) * z = z + z := by ring
        _ = z + (-z) := by
              exact congrArg (fun t : ℂ => z + t) h
        _ = 0 := by simp
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    exact hz_ne_zero ((mul_eq_zero.mp hmul).resolve_left h2ne)
  have hsame : quadratic_map c z = quadratic_map c (-z) := by
    simp [quadratic_map, pow_two]
  intro hinj
  exact hz_ne_negz (hinj hz_basin hnegz_basin hsame)

lemma not_quadratic_map_left_inverse_on_basin (c : ℂ) :
    ¬ HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  intro hleft
  have hinj : Set.InjOn (quadratic_map c) (basin_of_infinity c) :=
    injOn_of_hasLeftInverseOn hleft
  exact quadratic_map_not_injOn_basin c hinj

lemma not_quadratic_map_iter_eq_imp_eq (c : ℂ) :
    ¬ (∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) := by
  intro h_iter_eq_imp
  have h_inj : Set.InjOn (quadratic_map c) (basin_of_infinity c) := by
    intro z hz w hw hzw
    exact h_iter_eq_imp z w hz hw ⟨1, by simpa using hzw⟩
  exact quadratic_map_not_injOn_basin c h_inj

def BasinBottcherSquareRootRightInverse (c : ℂ) (sqrt : ℂ → ℂ) : Prop :=
  ∀ z, z ∈ basin_of_infinity c →
    sqrt ((bottcher_map c z) ^ 2) = bottcher_map c z

lemma quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  refine ⟨fun z => external_ray_map c (sqrt (bottcher_map c z)), ?_, ?_⟩
  · intro z hz
    have hsq : sqrt ((bottcher_map c z) ^ 2) = bottcher_map c z := h_sqrt z hz
    have hconj := h_conj z hz
    calc
      external_ray_map c (sqrt (bottcher_map c (quadratic_map c z)))
          = external_ray_map c (sqrt ((bottcher_map c z) ^ 2)) := by
              simp [hconj]
      _ = external_ray_map c (bottcher_map c z) := by simp [hsq]
      _ = z := h_left_bottcher z hz
  · intro z hz
    exact h_maps hz

lemma EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtensionHyp c := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch c sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact EventualSlitGlobalInverseExtensionHyp_of_left_inverse c hleft

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_basin_sqrt_branch
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  have h_ext :
      EventualSlitGlobalInverseExtensionHyp c :=
    EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch c sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext

lemma quadratic_map_iter_eq_imp_eq_of_basin_sqrt_branch
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_basin_sqrt_branch c sqrt h_sqrt
      h_conj h_left_bottcher h_maps
  exact quadratic_map_iter_eq_imp_eq_of_left_inverse c hleft

lemma bottcher_left_inverse_on_basin_of_injective
    (c : ℂ)
    (h_inj : Function.Injective (bottcher_map c)) :
    ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z := by
  intro z hz
  have hpos : 0 < green_function c z :=
    green_function_pos_of_basin c z hz
  have hnorm : 1 < ‖bottcher_map c z‖ :=
    bottcher_map_norm_gt_one_of_basin c z hz hpos
  exact bottcher_left_inv_of_injective c z hnorm h_inj

lemma EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch_of_injective
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_inj : Function.Injective (bottcher_map c))
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtensionHyp c := by
  have h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2 := by
    intro z hz
    exact bottcher_conj_on_basin c z hz
  have h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z :=
    bottcher_left_inverse_on_basin_of_injective c h_inj
  exact EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch c sqrt h_sqrt
    h_conj h_left_bottcher h_maps

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_basin_sqrt_branch_of_injective
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_inj : Function.Injective (bottcher_map c))
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  have h_ext :
      EventualSlitGlobalInverseExtensionHyp c :=
    EventualSlitGlobalInverseExtensionHyp_of_basin_sqrt_branch_of_injective c sqrt h_sqrt
      h_inj h_maps
  exact EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext

lemma quadratic_map_iter_eq_imp_eq_of_basin_sqrt_branch_of_injective
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : BasinBottcherSquareRootRightInverse c sqrt)
    (h_inj : Function.Injective (bottcher_map c))
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hiter :
      EventualSlitGlobalInverseExtendsToBasinIter c :=
    EventualSlitGlobalInverseExtendsToBasinIter_of_basin_sqrt_branch_of_injective c sqrt h_sqrt
      h_inj h_maps
  exact quadratic_map_iter_eq_imp_eq_of_extension_iter c hiter

def BasinQuadraticPullbackRoot (c : ℂ) (root : ℂ → ℂ) : Prop :=
  ∀ z, z ∈ basin_of_infinity c →
    root (quadratic_map c z) = bottcher_map c z

lemma quadratic_map_left_inverse_on_basin_of_pullback_root
    (c : ℂ)
    (root : ℂ → ℂ)
    (h_pull : BasinQuadraticPullbackRoot c root)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (root z))
      (basin_of_infinity c) (basin_of_infinity c)) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  refine ⟨fun z => external_ray_map c (root z), ?_, ?_⟩
  · intro z hz
    calc
      external_ray_map c (root (quadratic_map c z))
          = external_ray_map c (bottcher_map c z) := by
              simp [h_pull z hz]
      _ = z := h_left_bottcher z hz
  · intro z hz
    exact h_maps hz

lemma EventualSlitGlobalInverseExtensionHyp_of_pullback_root
    (c : ℂ)
    (root : ℂ → ℂ)
    (h_pull : BasinQuadraticPullbackRoot c root)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (root z))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtensionHyp c := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_pullback_root c root h_pull
      h_left_bottcher h_maps
  exact EventualSlitGlobalInverseExtensionHyp_of_left_inverse c hleft

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_pullback_root
    (c : ℂ)
    (root : ℂ → ℂ)
    (h_pull : BasinQuadraticPullbackRoot c root)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (root z))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  have h_ext :
      EventualSlitGlobalInverseExtensionHyp c :=
    EventualSlitGlobalInverseExtensionHyp_of_pullback_root c root h_pull h_left_bottcher h_maps
  exact EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext

lemma quadratic_map_iter_eq_imp_eq_of_pullback_root
    (c : ℂ)
    (root : ℂ → ℂ)
    (h_pull : BasinQuadraticPullbackRoot c root)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_maps : MapsTo (fun z => external_ray_map c (root z))
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_pullback_root c root h_pull
      h_left_bottcher h_maps
  exact quadratic_map_iter_eq_imp_eq_of_left_inverse c hleft

lemma exists_BasinQuadraticPullbackRoot_of_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∃ root : ℂ → ℂ, BasinQuadraticPullbackRoot c root := by
  rcases hleft with ⟨g, hleft, hmap⟩
  refine ⟨fun z => bottcher_map c (g z), ?_⟩
  intro z hz
  simp [hleft z hz]

lemma bottcher_left_inverse_on_basin_of_quadratic_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z := by
  have h_iter_eq_imp :
      ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
        (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w :=
    quadratic_map_iter_eq_imp_eq_of_left_inverse c hleft
  have h_inj_outside :
      Set.InjOn (bottcher_map c) (outside_disk c) :=
    bottcher_map_inj_on_outside_of_slit c h_iter_eq_imp
  have hpre :
      (bottcher_map c) ⁻¹' {w : ℂ | 1 < ‖w‖} ⊆ outside_disk c :=
    bottcher_map_preimage_exterior_subset_outside_of_basin c
      (by
        intro z hz
        simpa [outside_disk] using hz)
  intro z hz
  exact bottcher_left_inv_outside c hpre h_inj_outside z (by simpa [outside_disk] using hz)

lemma exists_pullback_root_data_of_left_inverse
    (c : ℂ)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∃ root : ℂ → ℂ,
      BasinQuadraticPullbackRoot c root ∧
      MapsTo (fun z => external_ray_map c (root z))
        (basin_of_infinity c) (basin_of_infinity c) := by
  rcases hleft with ⟨g, hleft, hmap⟩
  have h_left_bottcher :
      ∀ z, z ∈ basin_of_infinity c →
        external_ray_map c (bottcher_map c z) = z :=
    bottcher_left_inverse_on_basin_of_quadratic_left_inverse c ⟨g, hleft, hmap⟩
  refine ⟨fun z => bottcher_map c (g z), ?_, ?_⟩
  · intro z hz
    simp [hleft z hz]
  · intro z hz
    have hg : g z ∈ basin_of_infinity c := hmap z hz
    have hlg : external_ray_map c (bottcher_map c (g z)) = g z :=
      h_left_bottcher (g z) hg
    have hmem : external_ray_map c (bottcher_map c (g z)) ∈ basin_of_infinity c := by
      exact hlg.symm ▸ hg
    simpa using hmem

lemma exists_pullback_root_data_of_iter_eq_imp
    (c : ℂ)
    (h_iter_eq_imp : ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w) :
    ∃ root : ℂ → ℂ,
      BasinQuadraticPullbackRoot c root ∧
      MapsTo (fun z => external_ray_map c (root z))
        (basin_of_infinity c) (basin_of_infinity c) := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_iter_eq_imp c h_iter_eq_imp
  exact exists_pullback_root_data_of_left_inverse c hleft

lemma quadratic_map_iter_eq_imp_eq_of_sqrt_branch_slitPlaneRight
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn slitPlaneRight sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRight c sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact quadratic_map_iter_eq_imp_eq_of_left_inverse c hleft

lemma quadratic_map_iter_eq_imp_eq_of_sqrt_branch_slitPlaneRotRight
    (c : ℂ) (θ : ℝ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn (slitPlaneRotRight θ) sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRotRight c θ sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact quadratic_map_iter_eq_imp_eq_of_left_inverse c hleft

lemma not_bottcher_map_mem_slitPlaneRight_on_basin (c : ℂ) :
    ¬ (∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight) := by
  intro h_mem
  have hw : 1 < ‖(-2 : ℂ)‖ := by norm_num
  rcases (bottcher_map_surj c (-2 : ℂ) hw) with ⟨z, _hzdom, hzw⟩
  have hz_norm : 1 < ‖bottcher_map c z‖ := by
    rw [hzw]
    exact hw
  have hz_basin : z ∈ basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := z) hz_norm
  have hneg_mem : (-2 : ℂ) ∈ slitPlaneRight := by
    simpa [hzw] using h_mem z hz_basin
  have hneg_not_mem : (-2 : ℂ) ∉ slitPlaneRight := by
    simp [slitPlaneRight]
  exact hneg_not_mem hneg_mem

lemma no_sqrt_branch_slitPlaneRight_data_on_full_basin (c : ℂ) :
    ¬ ∃ sqrt : ℂ → ℂ,
      SquareRootRightInverseOn slitPlaneRight sqrt ∧
      (∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight) := by
  intro h
  rcases h with ⟨sqrt, _h_sqrt, h_mem⟩
  exact not_bottcher_map_mem_slitPlaneRight_on_basin c h_mem

lemma not_bottcher_map_mem_slitPlaneRotRight_on_basin (c : ℂ) (θ : ℝ) :
    ¬ (∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ) := by
  intro h_mem
  let w : ℂ := (-2 : ℂ) * Complex.exp (Complex.I * θ / 2)
  have hw : 1 < ‖w‖ := by
    have hw_norm : ‖w‖ = 2 := by
      dsimp [w]
      rw [norm_mul]
      have hExp1 : ‖Complex.exp (Complex.I * θ / 2)‖ = 1 := by
        calc
          ‖Complex.exp (Complex.I * θ / 2)‖ = Real.exp ((Complex.I * θ / 2).re) := by
            simpa using (Complex.norm_exp (Complex.I * θ / 2))
          _ = 1 := by simp
      simp [hExp1]
    linarith [hw_norm]
  rcases (bottcher_map_surj c w hw) with ⟨z, _hzdom, hzw⟩
  have hz_norm : 1 < ‖bottcher_map c z‖ := by
    rw [hzw]
    exact hw
  have hz_basin : z ∈ basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := z) hz_norm
  have hw_mem : w ∈ slitPlaneRotRight θ := by
    simpa [hzw] using h_mem z hz_basin
  have hexp_cancel :
      Complex.exp (Complex.I * θ / 2) * Complex.exp (-Complex.I * θ / 2) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hprod : w * Complex.exp (-Complex.I * θ / 2) = (-2 : ℂ) := by
    calc
      w * Complex.exp (-Complex.I * θ / 2)
          = (-2 : ℂ) * (Complex.exp (Complex.I * θ / 2) * Complex.exp (-Complex.I * θ / 2)) := by
              simp [w, mul_left_comm, mul_comm]
      _ = (-2 : ℂ) * 1 := by rw [hexp_cancel]
      _ = (-2 : ℂ) := by simp
  have hneg_mem : (-2 : ℂ) ∈ slitPlaneRight := by
    have hw_mem' : w * Complex.exp (-Complex.I * θ / 2) ∈ slitPlaneRight := by
      simpa [slitPlaneRotRight] using hw_mem
    exact hprod ▸ hw_mem'
  have hneg_not_mem : (-2 : ℂ) ∉ slitPlaneRight := by
    simp [slitPlaneRight]
  exact hneg_not_mem hneg_mem

lemma no_sqrt_branch_slitPlaneRotRight_data_on_full_basin (c : ℂ) (θ : ℝ) :
    ¬ ∃ sqrt : ℂ → ℂ,
      SquareRootRightInverseOn (slitPlaneRotRight θ) sqrt ∧
      (∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ) := by
  intro h
  rcases h with ⟨sqrt, _h_sqrt, h_mem⟩
  exact not_bottcher_map_mem_slitPlaneRotRight_on_basin c θ h_mem

lemma no_BasinBottcherSquareRootRightInverse (c : ℂ) :
    ¬ ∃ sqrt : ℂ → ℂ, BasinBottcherSquareRootRightInverse c sqrt := by
  intro h
  rcases h with ⟨sqrt, h_sqrt⟩
  have h2_norm : 1 < ‖(2 : ℂ)‖ := by norm_num
  rcases (bottcher_map_surj c (2 : ℂ) h2_norm) with ⟨z2, _hz2dom, hz2eq⟩
  have hz2_norm : 1 < ‖bottcher_map c z2‖ := by
    rw [hz2eq]
    exact h2_norm
  have hz2_basin : z2 ∈ basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := z2) hz2_norm
  have hs2 : sqrt ((2 : ℂ) ^ 2) = (2 : ℂ) := by
    simpa [hz2eq] using h_sqrt z2 hz2_basin
  have hneg2_norm : 1 < ‖(-2 : ℂ)‖ := by norm_num
  rcases (bottcher_map_surj c (-2 : ℂ) hneg2_norm) with ⟨zneg2, _hzneg2dom, hzneg2eq⟩
  have hzneg2_norm : 1 < ‖bottcher_map c zneg2‖ := by
    rw [hzneg2eq]
    exact hneg2_norm
  have hzneg2_basin : zneg2 ∈ basin_of_infinity c :=
    bottcher_map_norm_gt_one_implies_basin c (z := zneg2) hzneg2_norm
  have hsneg2 : sqrt ((-2 : ℂ) ^ 2) = (-2 : ℂ) := by
    simpa [hzneg2eq] using h_sqrt zneg2 hzneg2_basin
  have hsneg2' : sqrt ((2 : ℂ) ^ 2) = (-2 : ℂ) := by
    simpa using hsneg2
  have hcontra : (2 : ℂ) = (-2 : ℂ) := hs2.symm.trans hsneg2'
  have hneq : (2 : ℂ) ≠ (-2 : ℂ) := by norm_num
  exact hneq hcontra

lemma no_basin_sqrt_branch_data_on_full_basin (c : ℂ) :
    ¬ ∃ sqrt : ℂ → ℂ,
      BasinBottcherSquareRootRightInverse c sqrt ∧
      MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
        (basin_of_infinity c) (basin_of_infinity c) := by
  intro h
  rcases h with ⟨sqrt, h_sqrt, _h_maps⟩
  exact no_BasinBottcherSquareRootRightInverse c ⟨sqrt, h_sqrt⟩

lemma quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_extension
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtensionToIter c hA _hG) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  exact quadratic_map_iter_eq_imp_eq_of_extension_iter c h_ext

lemma quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_extension_hyp
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
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

/-!
Concrete bridge data (still missing): a global left inverse on the basin that
is explicitly realized by pulling back the eventual-slit inverse along some
escape time. This makes the remaining gap explicit without introducing `sorry`.
-/
noncomputable def eventualSlitEscapeTime (c : ℂ) (z : ℂ) : ℕ := by
  classical
  exact
    if hz : z ∈ basin_of_infinity c then
      Classical.choose (basin_eventually_in_eventual_slit c z hz)
    else 0

lemma eventualSlitEscapeTime_spec (c : ℂ) {z : ℂ}
    (hz : z ∈ basin_of_infinity c) :
    (quadratic_map c)^[eventualSlitEscapeTime c z] z ∈ eventual_slit_set c := by
  classical
  simpa [eventualSlitEscapeTime, hz] using
    (Classical.choose_spec (basin_eventually_in_eventual_slit c z hz))

noncomputable def eventualSlitBridgeCandidate (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) : ℂ → ℂ := by
  classical
  exact fun z =>
    if hz : z ∈ basin_of_infinity c then
      (Classical.choose hG)
        (bottcher_map c ((quadratic_map c)^[eventualSlitEscapeTime c z] z))
    else z

lemma eventualSlitBridgeCandidate_eq_escape_iterate
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    {z : ℂ} (hz : z ∈ basin_of_infinity c) :
    eventualSlitBridgeCandidate c hA hG z =
      (quadratic_map c)^[eventualSlitEscapeTime c z] z := by
  let N : ℕ := eventualSlitEscapeTime c z
  have hNslit : (quadratic_map c)^[N] z ∈ eventual_slit_set c := by
    simpa [N] using eventualSlitEscapeTime_spec c hz
  have hfiter :
      ∀ n, MapsTo (quadratic_map c)^[n] (basin_of_infinity c) (basin_of_infinity c) :=
    MapsTo.iterate (basin_of_infinity_forward_invariant c)
  have hNbasin : (quadratic_map c)^[N] z ∈ basin_of_infinity c :=
    (hfiter N) hz
  have hpoint :
      (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[N] z)) =
        (quadratic_map c)^[N] z :=
    bottcher_left_inverse_pointwise_on_eventual_slit_of_global_inverse c hA hG
      ((quadratic_map c)^[N] z) ⟨hNslit, hNbasin⟩
  have hcand :
      eventualSlitBridgeCandidate c hA hG z =
        (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[N] z)) := by
    classical
    simpa [N] using (by simp [eventualSlitBridgeCandidate, hz] :
      eventualSlitBridgeCandidate c hA hG z =
        (Classical.choose hG)
          (bottcher_map c ((quadratic_map c)^[eventualSlitEscapeTime c z] z)))
  exact hcand.trans hpoint

lemma eventualSlitBridgeCandidate_mem_basin
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    ∀ z, z ∈ basin_of_infinity c →
      eventualSlitBridgeCandidate c hA hG z ∈ basin_of_infinity c := by
  intro z hz
  have hfiter :
      ∀ n, MapsTo (quadratic_map c)^[n] (basin_of_infinity c) (basin_of_infinity c) :=
    MapsTo.iterate (basin_of_infinity_forward_invariant c)
  have hNbasin :
      (quadratic_map c)^[eventualSlitEscapeTime c z] z ∈ basin_of_infinity c :=
    (hfiter (eventualSlitEscapeTime c z)) hz
  exact (eventualSlitBridgeCandidate_eq_escape_iterate c hA hG hz) ▸ hNbasin

lemma eventualSlitBridgeCandidate_repr
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    ∀ z, z ∈ basin_of_infinity c →
      ∃ N, (quadratic_map c)^[N] z ∈ eventual_slit_set c ∧
        eventualSlitBridgeCandidate c hA hG z =
          (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[N] z)) := by
  intro z hz
  refine ⟨eventualSlitEscapeTime c z, eventualSlitEscapeTime_spec c hz, ?_⟩
  classical
  simp [eventualSlitBridgeCandidate, hz]

def EventualSlitBridgeCandidateLeftInverse (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) : Prop :=
  ∀ z, z ∈ basin_of_infinity c →
    eventualSlitBridgeCandidate c hA hG (quadratic_map c z) = z

def EventualSlitEscapeIterateLeftInverse (c : ℂ) : Prop :=
  ∀ z, z ∈ basin_of_infinity c →
    (quadratic_map c)^[eventualSlitEscapeTime c (quadratic_map c z)] (quadratic_map c z) = z

lemma iterate_mul_eq_self_of_iterate_eq_self
    {f : ℂ → ℂ} {z : ℂ} {p : ℕ} (hp : (f^[p]) z = z) :
    ∀ k : ℕ, (f^[p * k]) z = z := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        (f^[p * (k + 1)]) z = (f^[p * k + p]) z := by
          simp [Nat.mul_add, Nat.add_comm]
      _ = (f^[p]) ((f^[p * k]) z) := by
          simp [Function.iterate_add, Function.comp_apply, Nat.add_comm]
      _ = (f^[p]) z := by simp [ih]
      _ = z := hp

lemma not_mem_basin_of_periodic
    (c z : ℂ) {p : ℕ} (hp_pos : 0 < p)
    (hp : (quadratic_map c)^[p] z = z) :
    z ∉ basin_of_infinity c := by
  intro hz
  have ht : Tendsto (fun n => ‖(quadratic_map c)^[n] z‖) atTop atTop := by
    simpa [basin_of_infinity, MLC.basin_of_infinity] using hz
  have hlarge := (Filter.tendsto_atTop.1 ht) (‖z‖ + 1)
  rcases (Filter.eventually_atTop.1 hlarge) with ⟨N, hN⟩
  have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp_pos
  have hNle : N ≤ p * N := by
    simpa [one_mul] using (Nat.mul_le_mul_right N hp1)
  have hperiod : (quadratic_map c)^[p * N] z = z :=
    iterate_mul_eq_self_of_iterate_eq_self (f := quadratic_map c) (z := z) hp N
  have hbig : ‖(quadratic_map c)^[p * N] z‖ ≥ ‖z‖ + 1 := hN (p * N) hNle
  have hsmall : ‖(quadratic_map c)^[p * N] z‖ = ‖z‖ := by simp [hperiod]
  linarith [hbig, hsmall]

lemma not_EventualSlitEscapeIterateLeftInverse (c : ℂ) :
    ¬ EventualSlitEscapeIterateLeftInverse c := by
  intro hesc
  rcases basin_of_infinity_nonempty c with ⟨z, hz⟩
  let N : ℕ := eventualSlitEscapeTime c (quadratic_map c z)
  have hperiod_base :
      (quadratic_map c)^[N] (quadratic_map c z) = z := by
    simpa [N] using
      (hesc z hz)
  have hsucc :
      (quadratic_map c)^[N + 1] z = (quadratic_map c)^[N] (quadratic_map c z) := by
    exact (Function.iterate_succ_apply (f := quadratic_map c) (n := N) (x := z))
  have hperiod :
      (quadratic_map c)^[N + 1] z = z := by
    exact hsucc.trans hperiod_base
  have hp_pos : 0 < N + 1 := by
    exact Nat.succ_pos _
  exact not_mem_basin_of_periodic c z hp_pos hperiod hz

lemma EventualSlitBridgeCandidateLeftInverse_iff_escape_iterate
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    EventualSlitBridgeCandidateLeftInverse c hA hG ↔
      ∀ z, z ∈ basin_of_infinity c →
        (quadratic_map c)^[eventualSlitEscapeTime c (quadratic_map c z)] (quadratic_map c z) = z := by
  constructor
  · intro h z hz
    have hzq : quadratic_map c z ∈ basin_of_infinity c :=
      (basin_of_infinity_forward_invariant c) hz
    simpa [eventualSlitBridgeCandidate_eq_escape_iterate c hA hG hzq] using h z hz
  · intro h z hz
    have hzq : quadratic_map c z ∈ basin_of_infinity c :=
      (basin_of_infinity_forward_invariant c) hz
    simpa [eventualSlitBridgeCandidate_eq_escape_iterate c hA hG hzq] using h z hz

lemma EventualSlitBridgeCandidateLeftInverse_of_escape_iterate
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    (hesc : EventualSlitEscapeIterateLeftInverse c) :
    EventualSlitBridgeCandidateLeftInverse c hA hG :=
  (EventualSlitBridgeCandidateLeftInverse_iff_escape_iterate c hA hG).2 hesc

def EventualSlitGlobalInverseIterateCompatibility (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) : Prop :=
  ∀ z, z ∈ basin_of_infinity c →
    ∀ N M,
      (quadratic_map c)^[N] z ∈ eventual_slit_set c →
      (quadratic_map c)^[M] z ∈ eventual_slit_set c →
      (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[N] z)) =
        (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[M] z))

def EventualSlitGlobalInverseExtensionBridge (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) : Prop :=
  ∃ g : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → g (quadratic_map c z) = z) ∧
    (∀ z, z ∈ basin_of_infinity c → g z ∈ basin_of_infinity c) ∧
    (∀ z, z ∈ basin_of_infinity c →
      ∃ N, (quadratic_map c)^[N] z ∈ eventual_slit_set c ∧
        g z =
          (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[N] z)))

lemma EventualSlitGlobalInverseExtensionBridge_of_candidate_left_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    (hleft : EventualSlitBridgeCandidateLeftInverse c hA hG) :
    EventualSlitGlobalInverseExtensionBridge c hA hG := by
  refine ⟨eventualSlitBridgeCandidate c hA hG, ?_, ?_, ?_⟩
  · intro z hz
    exact hleft z hz
  · intro z hz
    exact eventualSlitBridgeCandidate_mem_basin c hA hG z hz
  · intro z hz
    exact eventualSlitBridgeCandidate_repr c hA hG z hz

lemma EventualSlitGlobalInverseExtensionBridge_of_escape_iterate
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA)
    (hesc : EventualSlitEscapeIterateLeftInverse c) :
    EventualSlitGlobalInverseExtensionBridge c hA hG := by
  exact EventualSlitGlobalInverseExtensionBridge_of_candidate_left_inverse c hA hG
    (EventualSlitBridgeCandidateLeftInverse_of_escape_iterate c hA hG hesc)

lemma not_EventualSlitGlobalInverseExtensionBridge
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (hG : GlobalInverseOnEventualSlit c hA) :
    ¬ EventualSlitGlobalInverseExtensionBridge c hA hG := by
  intro hbridge
  rcases hbridge with ⟨g, hleft, _hmap, hrepr⟩
  rcases basin_of_infinity_nonempty c with ⟨z, hz⟩
  have hzq : quadratic_map c z ∈ basin_of_infinity c :=
    (basin_of_infinity_forward_invariant c) hz
  rcases hrepr (quadratic_map c z) hzq with ⟨N, hNslit, hreprN⟩
  have hfiter :
      ∀ n, MapsTo (quadratic_map c)^[n] (basin_of_infinity c) (basin_of_infinity c) :=
    MapsTo.iterate (basin_of_infinity_forward_invariant c)
  have hNbasin : (quadratic_map c)^[N] (quadratic_map c z) ∈ basin_of_infinity c :=
    (hfiter N) hzq
  have hchoose :
      (Classical.choose hG) (bottcher_map c ((quadratic_map c)^[N] (quadratic_map c z))) =
        (quadratic_map c)^[N] (quadratic_map c z) :=
    bottcher_left_inverse_pointwise_on_eventual_slit_of_global_inverse c hA hG
      ((quadratic_map c)^[N] (quadratic_map c z)) ⟨hNslit, hNbasin⟩
  have hgq :
      g (quadratic_map c z) =
        (quadratic_map c)^[N] (quadratic_map c z) := hreprN.trans hchoose
  have hperiod_base :
      (quadratic_map c)^[N] (quadratic_map c z) = z := by
    calc
      (quadratic_map c)^[N] (quadratic_map c z) = g (quadratic_map c z) := hgq.symm
      _ = z := hleft z hz
  have hsucc :
      (quadratic_map c)^[N + 1] z = (quadratic_map c)^[N] (quadratic_map c z) :=
    Function.iterate_succ_apply (f := quadratic_map c) (n := N) (x := z)
  have hperiod : (quadratic_map c)^[N + 1] z = z := hsucc.trans hperiod_base
  have hp_pos : 0 < N + 1 := Nat.succ_pos _
  exact not_mem_basin_of_periodic c z hp_pos hperiod hz

def EventualSlitGlobalInverseExtendsToBasin (c : ℂ)
    (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA) : Prop :=
  ∃ g : ℂ → ℂ,
    (∀ z, z ∈ basin_of_infinity c → g (quadratic_map c z) = z) ∧
    (∀ z, z ∈ basin_of_infinity c → g z ∈ basin_of_infinity c)

lemma EventualSlitGlobalInverseExtendsToBasin_of_left_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (hleft : HasLeftInverseOn (quadratic_map c)
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasin c hA _hG := by
  rcases hleft with ⟨g, hleft, hmap⟩
  exact ⟨g, hleft, hmap⟩

lemma EventualSlitGlobalInverseExtendsToBasin_iff_left_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA) :
    EventualSlitGlobalInverseExtendsToBasin c hA _hG ↔
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  constructor
  · intro h_ext
    rcases h_ext with ⟨g, hleft, hmap⟩
    exact ⟨g, hleft, hmap⟩
  · intro hleft
    exact EventualSlitGlobalInverseExtendsToBasin_of_left_inverse c hA _hG hleft

lemma EventualSlitGlobalInverseExtensionHyp_of_sqrt_branch_slitPlaneRight
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn slitPlaneRight sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtensionHyp c := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRight c sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact EventualSlitGlobalInverseExtensionHyp_of_left_inverse c hleft

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_sqrt_branch_slitPlaneRight
    (c : ℂ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn slitPlaneRight sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  have h_ext :
      EventualSlitGlobalInverseExtensionHyp c :=
    EventualSlitGlobalInverseExtensionHyp_of_sqrt_branch_slitPlaneRight c sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext

lemma EventualSlitGlobalInverseExtendsToBasin_of_sqrt_branch_slitPlaneRight
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn slitPlaneRight sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRight)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasin c hA _hG := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRight c sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact EventualSlitGlobalInverseExtendsToBasin_of_left_inverse c hA _hG hleft

lemma EventualSlitGlobalInverseExtensionHyp_of_sqrt_branch_slitPlaneRotRight
    (c : ℂ) (θ : ℝ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn (slitPlaneRotRight θ) sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtensionHyp c := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRotRight c θ sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact EventualSlitGlobalInverseExtensionHyp_of_left_inverse c hleft

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_sqrt_branch_slitPlaneRotRight
    (c : ℂ) (θ : ℝ)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn (slitPlaneRotRight θ) sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  have h_ext :
      EventualSlitGlobalInverseExtensionHyp c :=
    EventualSlitGlobalInverseExtensionHyp_of_sqrt_branch_slitPlaneRotRight c θ sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext

lemma EventualSlitGlobalInverseExtendsToBasin_of_sqrt_branch_slitPlaneRotRight
    (c : ℂ) (θ : ℝ)
    (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (sqrt : ℂ → ℂ)
    (h_sqrt : SquareRootRightInverseOn (slitPlaneRotRight θ) sqrt)
    (h_conj : ∀ z, z ∈ basin_of_infinity c →
      bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2)
    (h_left_bottcher : ∀ z, z ∈ basin_of_infinity c →
      external_ray_map c (bottcher_map c z) = z)
    (h_mem : ∀ z, z ∈ basin_of_infinity c → bottcher_map c z ∈ slitPlaneRotRight θ)
    (h_maps : MapsTo (fun z => external_ray_map c (sqrt (bottcher_map c z)))
      (basin_of_infinity c) (basin_of_infinity c)) :
    EventualSlitGlobalInverseExtendsToBasin c hA _hG := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_sqrt_branch_slitPlaneRotRight c θ sqrt h_sqrt
      h_conj h_left_bottcher h_mem h_maps
  exact EventualSlitGlobalInverseExtendsToBasin_of_left_inverse c hA _hG hleft

lemma EventualSlitGlobalInverseExtendsToBasin_of_bridge
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_bridge : EventualSlitGlobalInverseExtensionBridge c hA _hG) :
    EventualSlitGlobalInverseExtendsToBasin c hA _hG := by
  rcases h_bridge with ⟨g, hleft, hmap, hbridge⟩
  exact ⟨g, hleft, hmap⟩

lemma quadratic_map_left_inverse_on_basin_of_global_inverse
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtendsToBasin c hA _hG) :
    HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) := by
  rcases h_ext with ⟨g, hleft, hmap⟩
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    exact hleft z hz
  · intro z hz
    exact hmap z hz

lemma exists_pullback_root_data_of_global_inverse_extension
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtendsToBasin c hA _hG) :
    ∃ root : ℂ → ℂ,
      BasinQuadraticPullbackRoot c root ∧
      MapsTo (fun z => external_ray_map c (root z))
        (basin_of_infinity c) (basin_of_infinity c) := by
  have hleft :
      HasLeftInverseOn (quadratic_map c) (basin_of_infinity c) (basin_of_infinity c) :=
    quadratic_map_left_inverse_on_basin_of_global_inverse c hA _hG h_ext
  exact exists_pullback_root_data_of_left_inverse c hleft

lemma exists_pullback_root_data_of_bridge
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_bridge : EventualSlitGlobalInverseExtensionBridge c hA _hG) :
    ∃ root : ℂ → ℂ,
      BasinQuadraticPullbackRoot c root ∧
      MapsTo (fun z => external_ray_map c (root z))
        (basin_of_infinity c) (basin_of_infinity c) := by
  have h_ext :
      EventualSlitGlobalInverseExtendsToBasin c hA _hG :=
    EventualSlitGlobalInverseExtendsToBasin_of_bridge c hA _hG h_bridge
  exact exists_pullback_root_data_of_global_inverse_extension c hA _hG h_ext

lemma orbit_inverse_branch_system_of_global_inverse_extension
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_ext : EventualSlitGlobalInverseExtendsToBasin c hA _hG) :
    OrbitInverseBranchSystem c := by
  have hleft :=
    quadratic_map_left_inverse_on_basin_of_global_inverse c hA _hG h_ext
  exact orbit_inverse_branch_system_of_left_inverse c hleft

lemma EventualSlitGlobalInverseExtensionHyp_of_bridge
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_bridge : EventualSlitGlobalInverseExtensionBridge c hA _hG) :
    EventualSlitGlobalInverseExtensionHyp c := by
  have h_ext :
      EventualSlitGlobalInverseExtendsToBasin c hA _hG :=
    EventualSlitGlobalInverseExtendsToBasin_of_bridge c hA _hG h_bridge
  have h_orbit :
      OrbitInverseBranchSystem c :=
    orbit_inverse_branch_system_of_global_inverse_extension c hA _hG h_ext
  exact eventual_slit_global_inverse_extension_hyp_of_orbit_system c h_orbit

lemma EventualSlitGlobalInverseExtendsToBasinIter_of_bridge
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_bridge : EventualSlitGlobalInverseExtensionBridge c hA _hG) :
    EventualSlitGlobalInverseExtendsToBasinIter c := by
  have h_ext_hyp :
      EventualSlitGlobalInverseExtensionHyp c :=
    EventualSlitGlobalInverseExtensionHyp_of_bridge c hA _hG h_bridge
  exact EventualSlitGlobalInverseExtendsToBasinIter_of_extension_hyp c h_ext_hyp

lemma quadratic_map_iter_eq_imp_eq_of_eventual_slit_global_bridge
    (c : ℂ) (hA : EventualSlitInverseAtlas c) (_hG : GlobalInverseOnEventualSlit c hA)
    (h_bridge : EventualSlitGlobalInverseExtensionBridge c hA _hG) :
    ∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
      (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w := by
  have hiter :
      EventualSlitGlobalInverseExtendsToBasinIter c :=
    EventualSlitGlobalInverseExtendsToBasinIter_of_bridge c hA _hG h_bridge
  exact quadratic_map_iter_eq_imp_eq_of_extension_iter c hiter

end Quadratic
end MLC
