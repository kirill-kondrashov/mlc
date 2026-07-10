# TASK 38 — Finite-level coherence of local Böttcher root branches (Stage 2A)

## Feasibility conclusion

The original Stage-2 idea “kill monodromy because the basin is simply
connected” is **not** a valid direct target:

- Mathlib does have `Complex.isCoveringMap_exp` and
  `IsCoveringMap.existsUnique_continuousMap_lifts`, so the covering-space tool
  itself is available.
- But the basin is a plane exterior domain in basic cases (already `c = 0`),
  not a simply connected plane subset. The correct root-existence mechanism is
  dynamical winding/divisibility, not a global logarithm on the basin.
- The existing `BasinLoopChartChainMonodromyData` is also too strong as an
  immediate target: it requires a zero-free chart chain at **every** level.
  This is impossible at `c = 2`, basepoint `0`, level `N = 0`, because the
  constant basin loop has root-equation value
  `logSeriesBottcherApprox 2 0 = 0`, while every chart is zero-free. This was
  formally verified in a temporary Lean probe.

Therefore this task is a corrected, realistic **Stage 2A**: establish the
finite-level compatibility of the local branches already landed in Stage 1.
It does not claim global monodromy triviality.

## Global context

The Böttcher route currently has:

- basin preconnectedness discharged unconditionally;
- Stage 1 landed:
  `localPullbackRootBranchData_of_iterate_outside`, producing a local
  holomorphic `2^N`-th-root branch whenever the `N`-th iterate is outside;
- the literal principal-`cpow` candidate still known to be discontinuous.

The mathematically correct next layer must preserve the same local branch while
raising the escape level. If the neighborhood remains in the level-`N`
outside-open region, then

`F_(N+1) = F_N^2`

and a branch satisfying `g^(2^N) = F_N` automatically satisfies
`g^(2^(N+1)) = F_(N+1)`. This is the finite-level compatibility needed before
any genuine loop/monodromy comparison can be attempted.

## Deliverable

Create a new leaf file:

`Mlc/BottcherFiniteLevelCoherence.lean`

Register it in `Mlc.lean` immediately after:

`import Mlc.BottcherLocalRootBranch`

Paste the following planner-verified content verbatim. It was compiled in a
temporary probe importing the current Stage-1 file (`PROBE_EXIT_0`).

```lean
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
```

## Constraints

- Do not edit `ConstructiveBasinCoordinate.lean`,
  `ConstructiveBasinModulus.lean`, or `Mlc/BottcherLocalRootBranch.lean`.
- Do not introduce `sorry`, `admit`, or new axioms.
- Do not claim this proves global monodromy triviality or `holo_on_basin`.
- Do not commit.

## Verification

Run:

1. `lake build`
2. `lake env lean check_axioms.lean`

Both must pass. The axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_38_FINITE_LEVEL_ROOT_COHERENCE.md`

Report that Stage 2A finite-level coherence is landed, and explicitly state
that the genuine global monodromy/coherent-value problem remains open. Mention
that the false simple-connectivity route and impossible all-level chart-chain
target were rejected for the reasons in this task.
