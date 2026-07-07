# PLAN 01: Prove `MLC.Quadratic.filled_julia_set_connected`

**Status:** ACTIVE  
**Depends on:** `PLAN_00_frontier_overview.md`

## Goal

Replace the axiom

```lean
MLC.Quadratic.filled_julia_set_connected
```

by a theorem without introducing any new axioms.

## Current formal state

The repository already contains a dedicated proof-development file:

```text
Mlc/FilledJuliaConnected.lean
```

Its intended theorem endpoint is:

```lean
filled_julia_set_connected_proved
```

The local topology lemma

```lean
isPreconnected_sq_preimage
```

is now proved without introducing new axioms. The remaining `sorry` is the final theorem surface

```lean
filled_julia_set_connected_proved
```

and the blocker is now precise rather than diffuse: the repository still lacks a surfaced non-circular bridge from an arbitrary parameter

```lean
c ∈ MLC.Quadratic.MandelbrotSet
```

to a decreasing family of compact preconnected approximants whose intersection is `K c`.

A direct session attempt was made via the escape-radius approximants

```lean
S n := {z | ‖orbit c z n‖ ≤ R c}
```

with the plan to prove `K c = ⋂ n, S n` and then apply the existing compact decreasing-intersection machinery. This clarified the exact obstruction: the proved local engine `isPreconnected_sq_preimage` only handles pullback under `z ↦ z^2`, while the real recursion for `S (n+1)` runs through the translated quadratic map `z ↦ z^2 + c`. So the missing bridge is not just compactness/intersection control, but specifically a non-circular way to propagate preconnectedness through the `+ c` term.

In particular, currently visible Yoccoz/principal-nest shrinkage theorems provide singleton intersections of dynamical puzzle pieces only under additional modulus-divergence hypotheses, while the Green-sublevel and para-puzzle routes remain circular with respect to the target axiom.

## Immediate task

Continue attacking `filled_julia_set_connected_proved` only through a non-circular bridge, for example by proving one of the following without new axioms:

1. an explicit identity `K c = ⋂ n, S n` for compact preconnected sets `S n`;
2. a direct bridge from `c ∈ MandelbrotSet` to the modulus-divergence hypothesis needed by the existing shrinkage theorems; or
3. a decircularized Green-sublevel / puzzle-piece equivalence that does not invoke `MLC.Quadratic.filled_julia_set_connected`.

## Success criterion

1. `filled_julia_set_connected_proved` is fully proved.
2. `make check` no longer reports `MLC.Quadratic.filled_julia_set_connected`.
3. No new non-core project axioms appear in its place.
