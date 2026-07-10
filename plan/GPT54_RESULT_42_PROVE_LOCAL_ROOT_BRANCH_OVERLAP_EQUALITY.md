# GPT-5.4 Result — Task 42: local root-branch overlap equality

## Outcome

Implemented the requested generic local overlap theorem, with no new axioms and no `sorry`s.

## Landed theorem

File: `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`

Added:

- `MLC.Quadratic.rootsOfUnitySet_countable`
- `MLC.Quadratic.localPullbackRootBranch_eqOn_of_eqAt`

The main theorem states that if

- `left right : LocalPullbackRootBranchData c N z₀`,
- `s` is preconnected,
- `s ⊆ left.U` and `s ⊆ right.U`,
- the common pullback target
  `logSeriesBottcherApprox c ((quadratic_map c)^[N] z)`
  is nonzero on `s`, and
- the two branches agree at one point `w₀ ∈ s`,

then `left.branch = right.branch` on all of `s` (`EqOn ... s`).

## Proof route

The proof is the finite-level local argument requested in the prompt:

1. Define the overlap ratio `right.branch / left.branch`.
2. Use the explicit nonvanishing hypothesis to show the denominator never vanishes, hence the ratio is continuous on `s`.
3. Use `pullbackRootSet_torsor_transitive` pointwise to show the ratio image lies in `rootsOfUnitySet (2 ^ N)`.
4. Prove `rootsOfUnitySet n` is countable for `n ≠ 0` by identifying it with the root set of `X^n - 1` and applying `Polynomial.finite_setOf_isRoot`.
5. Since a countable subset of `ℂ` is totally disconnected, the preconnected image of the ratio is subsingleton, so the ratio is constant.
6. Equality at one overlap point forces that constant to be `1`, giving branch equality on all of `s`.

## Why this is the right scope

This lands exactly the local-overlap ingredient needed before any later monodromy/loop argument.
It does **not** claim global monodromy triviality, and it does **not** introduce chart-chain hypotheses that are unnecessary for the local statement.

## Validation

Checked with:

- `lake env lean /tmp/task42_probe.lean`

The probe compiled the exact theorem in repository context before the source edit was applied.

## Remaining frontier after this task

Task 42 is now discharged locally. What remains for the broader branch/monodromy program is still global glue:

- transporting local equalities across finite covers/chains where needed;
- then, separately, the honest global obstruction already identified in Task 41 (whole-basin genuine Böttcher extension/evaluation).
