# TASK 39 — Arbitrary finite-level lifting of local Böttcher branches (Stage 2B)

## Global context

The Böttcher route currently has:

- basin preconnectedness discharged unconditionally;
- Stage 1 landed:
  `localPullbackRootBranchData_of_iterate_outside`;
- Stage 2A landed:
  `LocalPullbackRootBranchData.lift_one_level`, proving compatibility from
  level `N` to `N + 1` on one escaping neighborhood.

The literal principal-`cpow` basin candidate remains discontinuous. Global
monodromy triviality and `holo_on_basin` remain open. Do not revive the rejected
simple-connectivity route or the impossible all-level zero-free chart-chain
target.

This task extends the verified finite-level compatibility from one step to an
arbitrary finite number of steps. If the level-`N` neighborhood stays in the
outside-open region, forward invariance keeps every later level outside, so the
same local branch can be reused at level `N + d`.

## Deliverable

Create:

`Mlc/BottcherArbitraryFiniteLevelLift.lean`

Register it in `Mlc.lean` immediately after:

`import Mlc.BottcherFiniteLevelCoherence`

Paste the following planner-verified script verbatim. It compiled in a
temporary probe with `PROBE_EXIT_0`.

```lean
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
```

## Constraints

- Do not edit `ConstructiveBasinCoordinate.lean`,
  `ConstructiveBasinModulus.lean`, `BottcherLocalRootBranch.lean`, or
  `BottcherFiniteLevelCoherence.lean`.
- Do not introduce `sorry`, `admit`, or new axioms.
- Do not claim this proves global monodromy triviality, a global basin value, or
  `holo_on_basin`.
- Do not commit.

## Verification

Run:

1. `lake build`
2. `lake env lean check_axioms.lean`

Both must pass with the existing axiom frontier unchanged.

## Result report

Write:

`plan/GPT54_RESULT_39_ARBITRARY_FINITE_LEVEL_ROOT_LIFT.md`

Report that Stage 2B arbitrary finite-level local lifting is landed, while the
global loop/overlap comparison, coherent global value, and `holo_on_basin`
remain open.
