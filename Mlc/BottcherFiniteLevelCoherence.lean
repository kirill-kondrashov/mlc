import Mlc.BottcherLocalRootBranch

open MLC MLC.Quadratic Complex Topology Filter Set

namespace MLC.Quadratic

/-- A local root branch at an escaping level is automatically a valid branch at
the next level whenever its neighborhood remains in the escaping region. -/
noncomputable def LocalPullbackRootBranchData.lift_one_level
    {c : ℂ} {N : ℕ} {z₀ : ℂ}
    (D : LocalPullbackRootBranchData c N z₀)
    (houtside : ∀ z ∈ D.U,
      ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2) :
    LocalPullbackRootBranchData c (N + 1) z₀ := by
  refine
    { center_mem_basin := D.center_mem_basin
      U := D.U
      U_mem_nhds := D.U_mem_nhds
      branch := D.branch
      branch_differentiableOn := D.branch_differentiableOn
      root_eq := ?_
      center_value_mem_rootSet := ?_ }
  · intro z hz
    calc
      (D.branch z) ^ (2 ^ (N + 1)) = ((D.branch z) ^ (2 ^ N)) ^ 2 := by
        rw [show 2 ^ (N + 1) = (2 ^ N) * 2 by simp [pow_succ, Nat.mul_comm], pow_mul]
      _ = (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z)) ^ 2 := by
        rw [D.root_eq z hz]
      _ = MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N + 1] z) := by
        symm
        exact logSeriesBottcherApprox_iterate_succ_eq_sq c (houtside z hz)
  · have hz₀U : z₀ ∈ D.U := mem_of_mem_nhds D.U_mem_nhds
    have hroot := D.root_eq z₀ hz₀U
    have hnext := logSeriesBottcherApprox_iterate_succ_eq_sq c (houtside z₀ hz₀U)
    dsimp [pullbackRootSet]
    calc
      (D.branch z₀) ^ (2 ^ (N + 1)) = ((D.branch z₀) ^ (2 ^ N)) ^ 2 := by
        rw [show 2 ^ (N + 1) = (2 ^ N) * 2 by simp [pow_succ, Nat.mul_comm], pow_mul]
      _ = (MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N] z₀)) ^ 2 := by
        rw [hroot]
      _ = MLC.logSeriesBottcherApprox c ((MLC.quadratic_map c)^[N + 1] z₀) := hnext.symm

lemma localPullbackRootBranchData_of_iterate_outside_U_subset
    (c : ℂ) (N : ℕ) (z₀ : ℂ)
    (hz₀ : ‖(MLC.quadratic_map c)^[N] z₀‖ > ‖c‖ + 2) :
    ∀ z ∈ (localPullbackRootBranchData_of_iterate_outside c N z₀ hz₀).U,
      ‖(MLC.quadratic_map c)^[N] z‖ > ‖c‖ + 2 := by
  intro z hz
  exact hz.1

/-- Stage 2A: the Stage-1 branch has a canonical one-level coherent lift. -/
noncomputable def localPullbackRootBranchData_of_iterate_outside_lift_one_level
    (c : ℂ) (N : ℕ) (z₀ : ℂ)
    (hz₀ : ‖(MLC.quadratic_map c)^[N] z₀‖ > ‖c‖ + 2) :
    LocalPullbackRootBranchData c (N + 1) z₀ :=
  (localPullbackRootBranchData_of_iterate_outside c N z₀ hz₀).lift_one_level
    (localPullbackRootBranchData_of_iterate_outside_U_subset c N z₀ hz₀)

end MLC.Quadratic
