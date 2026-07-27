# Prompt 105 result: parameter-local chart data and higher-level lifts

## Status

Completed honestly in checked source.

## Checked source changes

File:

- `Mlc/ParameterCriticalOrbitLocal.lean`

Added:

- `ParameterCriticalOrbitLocalBranchData`
- `exists_parameterCriticalOrbitLocalBranchData`
- `ParameterCriticalOrbitLocalBranchData.root_eq_add`

## What is now proved

For every `c₀ ∉ MandelbrotSet`, the local existential branch from Prompt 104 is
now packaged as reusable concrete data containing:

- an escape level `N`
- an open parameter neighborhood `V` with `V ∈ 𝓝 c₀`
- a branch `G : ℂ → ℂ`
- `DifferentiableOn ℂ G V`
- the uniform exterior estimate
  `∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2`
- the base root identity
  `∀ c ∈ V, (G c) ^ (2 ^ N) = logSeriesBottcherApprox c (orbit c 0 (N + 1))`

Then, for the packaged data, the branch is coherent at every common future
escape level:

```lean
theorem ParameterCriticalOrbitLocalBranchData.root_eq_add
    {c₀ : ℂ} (D : ParameterCriticalOrbitLocalBranchData c₀) (k : ℕ) :
    ∀ c ∈ D.V,
      (D.G c) ^ (2 ^ (D.N + k)) =
        logSeriesBottcherApprox c (orbit c 0 (D.N + k + 1))
```

## Proof route

The proof is by induction on `k`.

- Base case `k = 0`: this is exactly `D.root_eq`.
- Successor step:
  - use the checked forward-invariance lemma
    `outside_iterate_add_of_outside`
    from `Mlc/BottcherArbitraryFiniteLevelLift.lean`
    to propagate the exterior bound from level `D.N + 1` to level
    `D.N + k + 1` on the same neighborhood;
  - apply `logSeriesBottcherApprox_iterate_succ_eq_sq` at that level;
  - square the induction hypothesis and rewrite exponents with `pow_mul`.

No new axioms, `sorry`, or parameter-loop claims were introduced.

## Validation

Ran successfully:

- `lake env lean Mlc/ParameterCriticalOrbitLocal.lean`
- `lake build`

## Frontier / limitation

This result gives **local all-future-level coherence on one fixed parameter
neighborhood**.

It does **not** yet provide:

- overlap-transition functions between two such parameter neighborhoods;
- parameter-loop continuation;
- trivial parameter monodromy on `MandelbrotSetᶜ`;
- any global parameter Böttcher coordinate.

So Prompt 105 is complete, while the overlap and monodromy layers identified in
Prompt 102 remain open.
