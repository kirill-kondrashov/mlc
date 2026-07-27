# Prompt 108 — finite parameter-loop transition product

## Status

Checked.

Targeted Lean check passed:

- `lake env lean Mlc/ParameterCriticalOrbitLoopProduct.lean` ✅

Build passed:

- `lake build` ✅

## Constructed and checked content

The file `Mlc/ParameterCriticalOrbitLoopProduct.lean` now contains a checked
finite loop-transition package based on the already validated Prompt 106/107
infrastructure. In particular it includes:

- `rootsOfUnitySet_mul_mem`
- `rootsOfUnitySet_listProd_mem`
- `ParameterCriticalOrbitLocalBranchData.overlap_transition_common_level`
- `ParameterLoopTransitionProductData`
- `ParameterLoopTransitionProductData.of_loop`

For a parameter path `γ` with endpoint condition `hγ : γ.path 0 = γ.path 1`,
the constructor now packages explicit finite data consisting of:

- the finite local-chart cover and finite mesh chain from Prompt 107;
- an explicit `baseChart` chosen around the loop basepoint `γ.path 0`;
- a single common finite level `level` dominating all chart levels occurring in
  the chain together with the base chart level;
- adjacent transition multipliers in `rootsOfUnitySet (2 ^ level)`;
- a closing multiplier in `rootsOfUnitySet (2 ^ level)` obtained from an
  explicit open ball around the loop basepoint inside the overlap of the last
  chart and the chosen base chart;
- the ordered finite product of the adjacent multipliers and the closing
  multiplier;
- a checked proof that this product also lies in `rootsOfUnitySet (2 ^ level)`.

## Important scope boundary

This prompt constructs a **finite transition product** attached to one chosen
finite chart chain for one chosen loop package. It does **not** prove any of the
following:

- that the product equals `1`;
- refinement invariance;
- independence of chart choices;
- homotopy invariance;
- a monodromy representation;
- a global parameter Böttcher coordinate;
- global continuation over `MandelbrotSetᶜ`.

So the checked result is exactly the finite-root-valued product construction,
not any triviality or invariance theorem.

## File-level handoff

Prompt 108 is now complete at the finite-product level requested by the prompt.
The next honest handoff, if continued later, is to a separate prompt proving
choice/refinement invariance or triviality only after the necessary additional
arguments are formalized.
