# GPT-5.4 Result — Task 43: align local root branches on overlap

## Outcome

Implemented the requested finite-level local alignment step.

## Landed declarations

File: `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`

Added:

- `MLC.Quadratic.LocalPullbackRootBranchData.rotate`
- `MLC.Quadratic.localPullbackRootBranch_eqOn_of_alignable`

## What the new theorem does

Given two local finite-level pullback branch data objects
`left right : LocalPullbackRootBranchData c N z₀`, a preconnected overlap `s`,
inclusions `s ⊆ left.U`, `s ⊆ right.U`, an overlap point `w₀ ∈ s`, and explicit
nonvanishing of the common pullback target on `s`, the theorem constructs an
`aligned` branch such that:

- `aligned` is obtained from `right` by multiplying by some
  `ζ ∈ rootsOfUnitySet (2 ^ N)`;
- `aligned.U = right.U`;
- `aligned.branch = fun z => ζ * right.branch z`; and
- `left.branch = aligned.branch` on all of `s`.

## Proof route

1. At the chosen overlap point `w₀`, both branch values solve the same equation
   `w^(2^N) = logSeriesBottcherApprox ...`.
2. Apply `pullbackRootSet_torsor_transitive` to obtain a multiplier
   `ζ ∈ rootsOfUnitySet (2 ^ N)` with
   `left.branch w₀ = ζ * right.branch w₀`.
3. Package `fun z => ζ * right.branch z` as a fresh
   `LocalPullbackRootBranchData` using the new constructor
   `LocalPullbackRootBranchData.rotate`.
4. Apply Task 42’s theorem `localPullbackRootBranch_eqOn_of_eqAt` to promote the
   pointwise equality at `w₀` to equality on the whole preconnected overlap.

## Scope control

This is still strictly a local finite-level alignment lemma. It does **not**
claim global monodromy triviality or any whole-basin continuation statement.
It is the normalization step needed before later finite-cover chain glue.

## Validation

Checked by compiling the edited source file:

- `lake env lean Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`

A dedicated probe was also compiled first to confirm the construction pattern.

## Remaining frontier after this task

The next work is to use this local alignment lemma along a finite branch cover /
chain, not yet to conclude any global uniqueness theorem without the required
finite-overlap transport argument.
