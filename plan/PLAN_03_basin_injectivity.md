# PLAN 03: Prove `MLC.proxy_bottcher_map_inj_on_basin_axiom`

**Status:** BLOCKED ON NEW MATHEMATICAL INPUT  
**Depends on:** `PLAN_00_frontier_overview.md`

## Goal

Replace

```lean
MLC.proxy_bottcher_map_inj_on_basin_axiom
```

by a theorem without introducing new axioms.

## Current formal state

The repository contains several theorem surfaces deriving basin injectivity from stronger inverse-branch or left-inverse packages, including theorems in the Böttcher and inverse-branch files.

However the currently available routes still require a hypothesis of the form

```lean
∀ z w, z ∈ basin_of_infinity c → w ∈ basin_of_infinity c →
  (∃ n, (quadratic_map c)^[n] z = (quadratic_map c)^[n] w) → z = w
```

or an equivalent all-iterates left-inverse package.

## Verified blocker

The repository already proves that the naive general iterate-equality implication is false as a blanket theorem:

```lean
not_quadratic_map_iter_eq_imp_eq
```

Therefore the current theorem surfaces do not yet provide an honest replacement for global basin injectivity.

## Required new idea

Any future proof must add genuine geometric input that rules out branch collisions on the relevant basin region, rather than deriving injectivity from the false global iterate-equality principle.

## Scope note

Do not replace this axiom by a disguised equivalent hypothesis. The task is to produce a theorem or to leave the axiom in place until new mathematics is formalized.
