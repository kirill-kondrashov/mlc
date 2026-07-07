# PLAN 05: Residual open virtual near-molecule package

**Status:** ALLOWED ENDPOINT  
**Depends on:** `PLAN_00_frontier_overview.md`

## Goal

Keep the only allowed non-core repository-specific open package in a mathematically explicit form:

```lean
MLC.residualOpenVirtualNearMoleculeAxiom
```

## Policy

This package is intended to formalize the remaining open Dudko-style obstruction to a full proof of MLC, namely the residual virtual near-molecule regime and the deduction of full MLC from Problems 4.3 and 4.4 together with the arguments from §4.1–§4.4.

All other non-core project axioms should be attacked and removed before revisiting whether this package can be further split or refined.

## Repository invariant

The target truthful endpoint for the repository is:

1. core Lean axioms only;
2. `MLC.residualOpenVirtualNearMoleculeAxiom` as the sole project-specific remaining mathematical input.
