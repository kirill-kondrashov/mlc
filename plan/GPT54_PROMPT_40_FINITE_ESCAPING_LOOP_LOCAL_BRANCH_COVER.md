Implement the task in
`plan/GPT54_TASK_40_FINITE_ESCAPING_LOOP_LOCAL_BRANCH_COVER.md`.

Based on the verified Stage 2B result, the next realistic bridge is compactness:
for a basin loop whose whole image lies in the outside-open region at level N,
extract a finite cover of the time interval by neighborhoods carrying the
Stage-1 local holomorphic root branches.

Create `Mlc/BottcherFiniteEscapingLoopCover.lean`, register it immediately after
`import Mlc.BottcherArbitraryFiniteLevelLift`, and paste the task script
verbatim. The payload compiled independently (`PROBE_EXIT_0`).

Run `lake build` and `lake env lean check_axioms.lean`; both must pass. Do not
edit prior Böttcher files, add `sorry`/`axiom`, or commit.

Be precise in the result: this lands only a finite local-branch cover. It does
not establish neighboring-branch equality, overlap multipliers, monodromy
triviality, a coherent global basin value, or `holo_on_basin`.

Write:

`plan/GPT54_RESULT_40_FINITE_ESCAPING_LOOP_LOCAL_BRANCH_COVER.md`
