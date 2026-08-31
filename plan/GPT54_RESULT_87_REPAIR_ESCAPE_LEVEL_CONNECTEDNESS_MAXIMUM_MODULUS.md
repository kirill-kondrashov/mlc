# GPT-54 Result 87 — Repair Escape Level Connectedness via Maximum-Modulus

## Outcome

Completed.

`Mlc/ParameterEscapeExhaustion.lean` now proves the finite-level parameter escape sets are
preconnected and connected:

- `isPreconnected_parameterEscapeLevel`
- `parameterEscapeLevel_isConnected`

without introducing axioms or using the incorrect identification with
`{c | R 0 < ‖orbit 0 c (n+1)‖}`.

## What changed

The first attempted specialization of `Mlc.BasinConnected.isPreconnected_orbit_superlevel`
was wrong because it implicitly identified the parameter orbit
`orbit c 0 (n + 1)` with the dynamical orbit `orbit 0 c (n + 1)`.
These are different maps in general.

The repaired proof instead reuses the **generic maximum-modulus separation pattern** from
`Mlc/BasinConnected.lean` directly for the parameter polynomial

`P(c) := orbit c 0 (n + 1)`.

Concretely:

1. `differentiable_orbit_zero_param` supplies holomorphy/differentiability of `P`.
2. `parameterEscapeLevel_zero` and `parameterEscapeLevel_mono` give the exterior inclusion
   `{c | 2 < ‖c‖} ⊆ ParameterEscapeLevel n`.
3. `exterior_preconnected (0 : ℂ)` supplies preconnectedness of the exterior seed.
4. `maxmod_absurd` and `frontier_side_subset_compl` are reused exactly as in
   `BasinConnected`, but instantiated at radius `R 0 = 2`.
5. A point in the exterior (`3 : ℂ`) provides nonemptiness, upgrading preconnectedness to
   connectedness.

## Validation

Targeted validation completed:

- `lake build Mlc.ParameterEscapeExhaustion`

Full-repo validation still needs to be run after this file creation:

- `make build`
- `make check`
- `./scripts/verify_output.sh`

## Notes

This closes the Prompt 87 repair honestly and without the stronger, unnecessary
polynomial-lemniscate route from Prompt 84.
