# MLC Formalization Status

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph (rooted at `MLC.mlc_conjecture`)](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository is a Lean formalization scaffold centered on `MLC.mlc_conjecture`.
The code compiles. One axiom blocks unconditional closure.

## Single remaining axiom

```
axiom external_ray_map_exists (c : ℂ) : ExternalRayMapData c
-- used only at c = 2
```

`ExternalRayMapData (2 : ℂ)` asks for `f : ℂ → ℂ` with:
- `bottcher_map 2 (f w) = w` for `‖w‖ > 1`
- `f (bottcher_map 2 z) = z` for `‖z‖ > 4`

## What the Böttcher map actually is (in this repo)

```lean
def bottcher_map c z := (z / ‖z‖) * exp(green_function c z)
```

This is the **polar Green map**: it preserves the argument of `z` and scales
the modulus by `exp(G_c(z))`. It is **not the standard analytic Böttcher
coordinate** — it is provably non-analytic (`not_outsideOpenAnalyticityHypothesisTwo`).

The proof: `bottcher_map(z)/z = exp(G(z))/‖z‖` is always a positive real;
an analytic function taking only positive real values on a connected region is
constant (open mapping theorem); but the quotient is not constant
(`not_outsideOpenQuotientConstHypothesisTwo`, proved numerically). Hence the
map is not analytic.

This closes all analytic/local-homeomorphism routes permanently in the current model.

## True constructive gap: Green function ray inversion

The inverse `f` must map each `w` to the unique `z` with:
- `arg(z) = arg(w)` (same direction)
- `G_2(z) = log ‖w‖` (matching Green function value)

This is the **external ray map**. To construct it, one needs:

1. **Monotonicity**: `G_2(ρ·e^{iθ})` is strictly increasing in `ρ` on `{ρ > 4}`.
2. **Surjectivity**: every Green value `t > 0` is attained on each ray.
3. **Inverse construction**: define `f(w)` as the unique ray preimage of `log‖w‖`.

For `c = 2`, the Green function has an explicit Chebyshev-type formula which
may make monotonicity tractable in Lean.

See `plan/PLAN_green_function_ray_inversion_c2.md` for the detailed plan.

## No prior formalization found

Exhaustive arXiv and MathOverflow searches for any Lean/Coq formalization of
Böttcher inverse / external ray existence returned zero results.
The mathematics is classical (Böttcher 1904, Milnor Ch. 9) but not yet
formalized in any proof assistant.

## Where to work

- Replacement point: `external_ray_map_exists_two_constructive` in
  `Mlc/MainConjecture.lean` (line ~3690)
- New target file: `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
- Active plan: `plan/PLAN_green_function_ray_inversion_c2.md`
- Axiom declaration: `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean` line 97

## Verification

```bash
make build && make check
```

Current `make check` output (expected until axiom is eliminated):
- `Quot.sound`
- `propext`
- `Classical.choice`
- `MLC.Quadratic.external_ray_map_exists`

Output:
```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.external_ray_map_exists
```
