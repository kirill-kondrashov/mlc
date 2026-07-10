import Mlc.BottcherFiniteLevelCoherence
open MLC MLC.Quadratic Complex Topology Filter Set
namespace MLC.Quadratic
lemma outside_iterate_add_of_outside
    (c z : ℂ) (N d : ℕ)
    (h : ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2) :
    ‖(MLC.quadratic_map c)^[N + d] z‖ > ‖c‖ + 2 := by
  have hd := MLC.quadratic_map_iter_maps_outside_open c h d
  rw [Nat.add_comm N d]
  simpa [Function.iterate_add, Function.comp_apply] using hd

lemma exists_localPullbackRootBranchData_lift_levels
    {c : ℂ} {N : ℕ} {z₀ : ℂ}
    (D : LocalPullbackRootBranchData c N z₀)
    (houtside : ∀ z ∈ D.U,
      ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2) :
    ∀ d : ℕ, ∃ E : LocalPullbackRootBranchData c (N + d) z₀,
      E.U = D.U ∧ E.branch = D.branch ∧
      ∀ z ∈ E.U, ‖(MLC.quadratic_map c)^[N + d] z‖ > ‖c‖ + 2 := by
  intro d
  induction d with
  | zero => exact ⟨D, rfl, rfl, houtside⟩
  | succ d ih =>
      rcases ih with ⟨E, hEU, hEbranch, hEout⟩
      let Enext : LocalPullbackRootBranchData c (N + (d + 1)) z₀ := by
        simpa [Nat.add_assoc] using E.lift_one_level hEout
      have hUE : Enext.U = E.U := by
        change E.U = E.U
        rfl
      have hUbranch : Enext.branch = E.branch := by
        change E.branch = E.branch
        rfl
      refine ⟨Enext, hUE.trans hEU, hUbranch.trans hEbranch, ?_⟩
      intro z hz
      have hzE : z ∈ E.U := by
        rw [← hUE]
        exact hz
      exact outside_iterate_add_of_outside c z (N + d) 1 (hEout z hzE)

/-- Stage 2B: canonical arbitrary finite-level lift of the Stage-1 branch. -/
noncomputable def localPullbackRootBranchData_of_iterate_outside_lift_levels
    (c : ℂ) (N d : ℕ) (z₀ : ℂ)
    (hz₀ : ‖(MLC.quadratic_map c)^[N] z₀‖ > ‖c‖ + 2) :
    LocalPullbackRootBranchData c (N + d) z₀ := by
  let D : LocalPullbackRootBranchData c N z₀ :=
    localPullbackRootBranchData_of_iterate_outside c N z₀ hz₀
  have hD : ∀ z ∈ D.U,
      ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2 := by
    simpa [D] using
      (localPullbackRootBranchData_of_iterate_outside_U_subset c N z₀ hz₀)
  exact Classical.choose (exists_localPullbackRootBranchData_lift_levels D hD d)

end MLC.Quadratic
