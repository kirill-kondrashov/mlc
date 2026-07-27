# GPT-5.4 Result 103 — parameter critical-orbit local germ gate

## Verdict

**Prompt 103 is already implementable from checked source.**
The first missing theorem is **not** joint/full near-infinity holomorphy: that gate has been crossed by the existing joint `ℂ²` differentiability package in
`Mlc/Quadratic/Complex/Bottcher/BottcherJointDeriv.lean`.

What remains is only to package the parameter-neighborhood analogue of the fixed-parameter constructor
`localPullbackRootBranchData_of_iterate_outside` from `Mlc/BottcherLocalRootBranch.lean`.

## Checked ingredients now available

### 1. Parameter differentiability of the orbit map

`ParameterEscapeExhaustion.lean` already provides

- `differentiable_orbit_zero_param (n : ℕ) : Differentiable ℂ (fun c => orbit c 0 n)`.

Hence for fixed `N`,

- `c ↦ orbit c 0 (N + 1)`

is a checked holomorphic parameter map.

### 2. Joint near-infinity differentiability of the Böttcher coordinate

The decisive source fact is already present in
`BottcherJointDeriv.lean`:

- `logSeriesBottcherApprox_differentiableAt_joint`
- `logSeriesBottcherApprox_contDiffAt_one_joint`

In particular, on an exterior polydisc,

- `(c,z) ↦ logSeriesBottcherApprox c z`

is jointly `ℂ`-differentiable, not merely separately differentiable or jointly continuous.
That is exactly strong enough to compose with the orbit map.

### 3. Explicit local root-branch template

`BottcherLocalRootBranch.lean` already contains the full explicit logarithm/root pattern:

- build `F`
- shrink to a neighborhood where `‖F/F(z₀)-1‖ < 1`
- use `Complex.log`
- define the branch by `Complex.exp ((Complex.log (...) + Complex.log (F z₀)) / (2 ^ N))`.

So Prompt 103 does not require a new abstract germ contract.

### 4. Basin escape engine available once the critical value is known to escape

`ConstructiveBasinCoordinate.lean` already provides

- `exists_iterate_mem_outside_open_of_mem_basin`.

Thus, once one supplies the standard bridge
`c₀ ∉ MandelbrotSet → c₀ ∈ basin_of_infinity c₀`,
one obtains `N` with

```lean
‖orbit c₀ 0 (N + 1)‖ > ‖c₀‖ + 2.
```

## Exact composite enabled by the checked API

For a chosen escape level `N`, set

```lean
F c := logSeriesBottcherApprox c (orbit c 0 (N + 1)).
```

Then the composite differentiability needed by the prompt follows from:

1. `c ↦ (c, orbit c 0 (N + 1))` is differentiable;
2. by continuity, after shrinking to a small parameter neighborhood `V` of `c₀`, the graph point
   `(c, orbit c 0 (N + 1))` stays inside some exterior polydisc around
   `(c₀, orbit c₀ 0 (N + 1))`;
3. `logSeriesBottcherApprox_differentiableAt_joint` applies there pointwise;
4. composition yields `DifferentiableOn ℂ F V`.

So the prompt’s key requirement — differentiability of the **composite** near-infinity family, not just fixed-`z` parameter differentiability — is formally supported by checked source.

## What should be implemented next in source

A parameter-local analogue of `localPullbackRootBranchData_of_iterate_outside` with data:

- `c₀ ∉ MandelbrotSet`
- an escape level `N`
- an open neighborhood `V ∋ c₀`
- `G : ℂ → ℂ`

such that

```lean
DifferentiableOn ℂ G V
∀ c ∈ V, (G c) ^ (2 ^ N) = logSeriesBottcherApprox c (orbit c 0 (N + 1)).
```

The proof is a one-variable replay of `BottcherLocalRootBranch.lean`, replacing the dynamical variable `z` by the parameter variable `c`, and replacing `F z` there by the composite above.

## Honest frontier status

Therefore Prompt 103 is **not blocked by missing joint holomorphy**.
The remaining work is packaging and proving the local-neighborhood statement in Lean. No new axiom, no global continuation, and no whole-basin extension is needed for this gate.
