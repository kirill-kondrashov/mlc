# RESULT 36 — Discharge basin preconnectedness

Task 36 is complete.

## What landed

Appended to the existing leaf file:

- `Mlc/BasinConnected.lean`

exactly the requested declaration block:

- `differentiable_orbit`
- `exterior_subset_superlevel`
- `exterior_preconnected`
- `maxmod_absurd`
- `frontier_side_subset_compl`
- `isPreconnected_orbit_superlevel`
- `basin_of_infinity_isPreconnected`

The final theorem now available is:

- `basin_of_infinity_isPreconnected (c : ℂ) : IsPreconnected (basin_of_infinity c)`

for every parameter `c`, with no residual hypotheses.

## Mathematical effect

This fully discharges the basin-preconnectedness residual that remained after
iteration 35.

The proof follows the intended maximum-modulus route:

- for each `n`, the orbit polynomial `z ↦ orbit c z n` is entire;
- the orbit-norm superlevel set `{z | R c < ‖orbit c z n‖}` contains the far exterior;
- any hypothetical separation forces one side to avoid the exterior, hence be bounded;
- on that bounded side, `‖orbit c · n‖` is `> R c` inside and `≤ R c` on the frontier;
- `Complex.exists_mem_frontier_isMaxOn_norm` gives the contradiction.

Combined with iteration 35’s assembly lemma
`basin_preconnected_of_forall_superlevel_preconnected`, this yields the
unconditional theorem `basin_of_infinity_isPreconnected`.

## Consequence for the Böttcher route

Iteration 34 showed:

- `coherentBasinCoordinate_conj_of_holo_of_preconnected`

so conjugacy on the basin follows from holomorphicity plus basin
preconnectedness.

Since basin preconnectedness is now unconditional, the `conj` obligation is now
formally derivable. Therefore the **only remaining residual** on the genuine
Böttcher-coordinate route is:

- `holo_on_basin`

namely, holomorphicity of the coherent branch on `basin_of_infinity c`.

## Validation

Passed:

- `lake build` → success (`7982` jobs)
- `lake env lean check_axioms.lean` → exit code `0`

As predicted by the task, there is one harmless local linter warning in
`Mlc/BasinConnected.lean`:

- `linter.unnecessarySimpa` at the `exterior_preconnected` `simpa` line

This was left unchanged.

## `sorry` / `axiom` status

No new declaration-level `sorry` or `axiom` was introduced.

The axiom frontier remains unchanged: exactly the two project axioms (plus the
already-allowed standard logical / classical axioms tracked by
`check_axioms.lean`).

## Scope discipline

As requested:

- `ConstructiveBasinCoordinate.lean` was untouched;
- `ConstructiveBasinModulus.lean` was untouched;
- the existing reduction lemma and imports in `Mlc/BasinConnected.lean` were left intact;
- no commit was made.
