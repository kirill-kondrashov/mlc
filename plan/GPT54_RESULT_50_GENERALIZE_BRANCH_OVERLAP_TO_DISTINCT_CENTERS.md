# Task 50 — Generalize Branch Overlap to Distinct Centers

## Outcome

Completed in `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`.

## What changed

Generalized the two local finite-level overlap/alignment lemmas from a common
center parameter `z₀` to arbitrary centers `z₁` and `z₂`:

- `localPullbackRootBranch_eqOn_of_eqAt`
- `localPullbackRootBranch_eqOn_of_alignable`

The new signatures are of the form:

- `left : LocalPullbackRootBranchData c N z₁`
- `right : LocalPullbackRootBranchData c N z₂`

with the same overlap hypotheses:

- preconnected overlap set `s`;
- `s ⊆ left.U` and `s ⊆ right.U`;
- nonvanishing of the common pullback target on `s`;
- equality at one overlap point for the `EqOn` theorem, or no pointwise equality
  assumption for the alignment theorem.

## Why this works

The proofs already depended only on:

- the branch functions;
- the domains `U`;
- differentiability on those domains;
- the common pullback equation;
- nonvanishing of the target.

None of those arguments use equality of the center parameters. The center only
matters in the ambient `LocalPullbackRootBranchData` packaging through
`center_mem_basin`, `U_mem_nhds`, and `center_value_mem_rootSet`, so the proof
strategy from Result 42/43 carries over unchanged.

## Proof notes

- The `EqOn` theorem still proves constancy of the overlap ratio into the finite
  root-of-unity set and then pins that ratio to `1` using one overlap point.
- The alignment theorem still chooses the torsor multiplier at one overlap point,
  rotates the right branch by that `2^N`-th root of unity, and applies the
  generalized `EqOn` theorem.
- The only implementation repair needed was to keep the aligned branch centered
  at `z₂`, i.e. as `LocalPullbackRootBranchData c N z₂`, because `rotate`
  preserves the original center.

## Compatibility

The previous same-center use cases remain immediate instances of the new
statements by setting `z₁ = z₂`.

## Validation

Targeted validation passed:

- `lake env lean Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`
