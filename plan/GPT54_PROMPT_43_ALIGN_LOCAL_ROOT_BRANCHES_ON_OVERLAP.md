Complete the active-frontier task in
`plan/GPT54_TASK_43_ALIGN_LOCAL_ROOT_BRANCHES_ON_OVERLAP.md`.

Result 42 successfully landed
`MLC.Quadratic.localPullbackRootBranch_eqOn_of_eqAt`, proving equality of two
finite-level local root branches on a connected overlap once they agree at one
point. The next honest local-glue step is to construct the required agreement
point normalization rather than adding it as an abstract field.

For two finite-level local branch data objects solving the same pullback
equation, with an explicit overlap point where both domains meet and the common
target is nonzero:

1. use `pullbackRootSet_torsor_transitive` to obtain the root-of-unity multiplier
   relating the two branch values at that point;
2. rotate one branch by that multiplier;
3. package the rotated branch as valid `LocalPullbackRootBranchData`;
4. apply the Result 42 overlap theorem to obtain equality on the connected
   overlap.

This should be a reusable local continuation/alignment lemma for later finite
cover chains. Keep it finite-level and local. Do not attempt to prove global
monodromy triviality, whole-basin Böttcher extension, parameter external
uniformization, or connectivity of the frozen Green set.

If the construction cannot be completed without a missing algebraic or
topological theorem, do not add `sorry`, `admit`, a new axiom, or an abstract
alignment field. Report the exact blocker and the smallest repair.

Write the worker report to:

`plan/GPT54_RESULT_43_ALIGN_LOCAL_ROOT_BRANCHES_ON_OVERLAP.md`

Do not edit unrelated files or commit.
