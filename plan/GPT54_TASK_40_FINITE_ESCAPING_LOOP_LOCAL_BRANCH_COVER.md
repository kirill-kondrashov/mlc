# TASK 40 — Finite local-branch cover of an escaping basin loop (Stage 2C)

## Global context

The Böttcher route currently has:

- unconditional basin preconnectedness;
- Stage 1 local holomorphic root branches;
- Stage 2A one-step finite-level coherence;
- Stage 2B arbitrary finite-level lifting.

The remaining problem is genuinely global: compare local branches around loops
and overlaps, construct a coherent basin value, and discharge `holo_on_basin`.

This task lands the next honest bridge: for a continuous basin loop whose whole
image is outside at level `N`, use compactness of `Icc (0,1)` to extract a
finite cover by neighborhoods carrying Stage-1 local root branches. This is
only a finite cover. It does **not** prove that neighboring branches agree,
does **not** compute overlap multipliers, and does **not** prove monodromy
triviality.

## Deliverable

Create:

`Mlc/BottcherFiniteEscapingLoopCover.lean`

Register it in `Mlc.lean` immediately after:

`import Mlc.BottcherArbitraryFiniteLevelLift`

Paste this planner-verified script verbatim. It compiled independently
(`PROBE_EXIT_0`).

```lean
import Mlc.BottcherArbitraryFiniteLevelLift
open MLC MLC.Quadratic Complex Topology Filter Set
namespace MLC.Quadratic
structure BasinLoopFiniteLocalRootBranchCover
    (c : ℂ) (N : ℕ) (z₀ : ℂ) (γ : BasinLoop c z₀) where
  centers : Finset {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  branchData : ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
    LocalPullbackRootBranchData c N (γ.path t)
  cover : ∀ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1},
    ∃ s ∈ centers, γ.path t ∈ (branchData s).U

noncomputable def BasinLoopFiniteLocalRootBranchCover.of_level_escapes
    {c : ℂ} {N : ℕ} {z₀ : ℂ} (γ : BasinLoop c z₀)
    (hesc : BasinLoopLevelEscapes c N γ) :
    BasinLoopFiniteLocalRootBranchCover c N z₀ γ := by
  let I : Type := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  let houtside : ∀ t : I,
      ‖(MLC.quadratic_map c)^[N] (γ.path t)‖ > ‖c‖ + 2 := by
    intro t
    exact hesc t.1 t.2
  let D : ∀ t : I, LocalPullbackRootBranchData c N (γ.path t) := by
    intro t
    exact localPullbackRootBranchData_of_iterate_outside c N (γ.path t) (houtside t)
  let V : ∀ t : I, Set I := fun t =>
    (fun s : I => γ.path s) ⁻¹' interior (D t).U
  have hpath : Continuous (fun s : I => γ.path s) := by
    exact (continuousOn_iff_continuous_restrict).1 (by
      simpa using γ.continuousOn_path)
  have hVo : ∀ t : I, IsOpen (V t) := by
    intro t
    exact isOpen_interior.preimage hpath
  have hVcover : (Set.univ : Set I) ⊆ ⋃ t : I, V t := by
    intro s _hs
    have hs_interior : γ.path s ∈ interior (D s).U :=
      mem_interior_iff_mem_nhds.mpr (D s).U_mem_nhds
    exact Set.mem_iUnion.2 ⟨s, hs_interior⟩
  let S : Finset I := Classical.choose (isCompact_univ.elim_finite_subcover V hVo hVcover)
  have hS : (Set.univ : Set I) ⊆ ⋃ t ∈ S, V t :=
    Classical.choose_spec (isCompact_univ.elim_finite_subcover V hVo hVcover)
  refine { centers := S, branchData := fun t => D t, cover := ?_ }
  intro t
  have htS : t ∈ ⋃ s ∈ S, V s := hS (by simp)
  rcases Set.mem_iUnion.1 htS with ⟨s, htS⟩
  rcases Set.mem_iUnion.1 htS with ⟨hsS, htVs⟩
  refine ⟨s, hsS, ?_⟩
  exact interior_subset htVs
end MLC.Quadratic
```

## Constraints

- Do not edit `ConstructiveBasinCoordinate.lean`,
  `ConstructiveBasinModulus.lean`, `BottcherLocalRootBranch.lean`,
  `BottcherFiniteLevelCoherence.lean`, or
  `BottcherArbitraryFiniteLevelLift.lean`.
- Do not introduce `sorry`, `admit`, or new axioms.
- Do not add any overlap-equality, branch-identification, or monodromy claim.
- Do not commit.

## Verification

Run:

1. `lake build`
2. `lake env lean check_axioms.lean`

Both must pass with the existing axiom frontier unchanged.

## Result report

Write:

`plan/GPT54_RESULT_40_FINITE_ESCAPING_LOOP_LOCAL_BRANCH_COVER.md`

State that Stage 2C provides a finite local-branch cover for each uniformly
escaping loop. Explicitly state that overlap compatibility, monodromy
triviality, coherent global values, and `holo_on_basin` remain open.
