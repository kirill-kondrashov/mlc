Complete the active-frontier task in
`plan/GPT54_TASK_50_GENERALIZE_BRANCH_OVERLAP_TO_DISTINCT_CENTERS.md`.

Result 49 completed the explicit `BasinLoopMeshChain`. Its neighboring cells
carry actual `LocalPullbackRootBranchData` objects centered at different loop
times. The current Result 42/43 overlap and alignment theorems are therefore
too narrowly typed: both branches have the same center parameter `z₀`.

Generalize the local finite-level overlap API so it applies to:

```lean
left  : LocalPullbackRootBranchData c N z₁
right : LocalPullbackRootBranchData c N z₂
```

with arbitrary centers `z₁` and `z₂`, provided their domains have a connected
overlap and the common pullback target is nonzero there. The equations and
differentiability fields do not depend on the center, so the proof should
reuse the existing Result 42/43 argument rather than duplicate it.

Land:

1. a generalized `EqOn` overlap theorem from equality at one overlap point;
2. a generalized root-of-unity rotation/alignment theorem;
3. compatibility corollaries for the existing same-center statements if
   necessary.

Do not build the full continuation chain yet. Do not alter the meaning of
`BasinLoopMeshChain`, invoke the vacuous value-space chart chain, or claim
monodromy triviality. If the current structures prevent this generalization,
report the exact type-level repair required rather than using casts or
`as`-style assertions.

Write the worker report to:

`plan/GPT54_RESULT_50_GENERALIZE_BRANCH_OVERLAP_TO_DISTINCT_CENTERS.md`

Do not add `sorry`, `admit`, or axioms, do not edit unrelated files, and do not
commit.
