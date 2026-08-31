# Prompt 101 result: critical-orbit escape-time coherence gate

## Status

Completed in checked source.

`Mlc/ParameterCriticalOrbitLocal.lean` now exports the parameter-local
successor-coherence theorem

- `exists_parameterCriticalOrbitLocalRootBranch_coherentSucc`

and the underlying Prompt 104 theorem

- `exists_parameterCriticalOrbitLocalRootBranch`

was strengthened to also export the strict exterior inequality on the same
parameter neighborhood.

## Checked theorem

The new theorem has the requested local shape:

```lean
theorem exists_parameterCriticalOrbitLocalRootBranch_coherentSucc
    (c₀ : ℂ) (hc₀ : c₀ ∉ MandelbrotSet) :
    ∃ N : ℕ, ∃ V : Set ℂ, ∃ G : ℂ → ℂ,
      V ∈ 𝓝 c₀ ∧ IsOpen V ∧ DifferentiableOn ℂ G V ∧
      (∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2) ∧
      (∀ c ∈ V,
        (G c) ^ (2 ^ N) =
          logSeriesBottcherApprox c (orbit c 0 (N + 1))) ∧
      (∀ c ∈ V,
        (G c) ^ (2 ^ (N + 1)) =
          logSeriesBottcherApprox c (orbit c 0 (N + 2))).
```

So a single local parameter-space branch `G` simultaneously realizes the level
`N` and level `N + 1` critical-orbit pullback identities on the same open
neighborhood `V` of the base parameter `c₀`.

## Proof route

The implementation reuses the exact branch and neighborhood constructed in the
Prompt 104 proof.

1. Prompt 104 already constructed `N`, an open ball `V`, and a branch `G` with
   `DifferentiableOn ℂ G V`.
2. That proof also already established the strict exterior estimate
   `∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2`; this estimate is now exported as
   part of `exists_parameterCriticalOrbitLocalRootBranch`.
3. For the successor identity, the new theorem:
   - raises the level-`N` root identity to the second power;
   - applies the checked theorem
     `logSeriesBottcherApprox_iterate_succ_eq_sq`;
   - rewrites iterates back to `orbit c 0 (N + 1)` and `orbit c 0 (N + 2)` via
     the existing orbit/iterate identities.

No comparison of arbitrary separately normalized roots is needed: the same
branch `G` works at both successive escape times.

## Validation

Checked successfully with:

- `lake env lean Mlc/ParameterCriticalOrbitLocal.lean`
- `lake build`

Both passed. The build emitted only pre-existing linter warnings, plus one local
`simpa` style warning in `Mlc/ParameterCriticalOrbitLocal.lean`.

## Limitations

This remains a local theorem near a fixed escaping parameter `c₀`.
It does **not** claim:

- global continuation of the branch;
- trivial monodromy;
- a whole-basin coordinate;
- parameter rays;
- elimination of any global frontier axiom.

Prompt 101 is now discharged at the intended local finite escape-time coherence
level.
