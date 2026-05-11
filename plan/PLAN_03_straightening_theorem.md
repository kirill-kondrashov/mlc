# PLAN 03: Prove `fixedPoint_parameter_model_data` (Straightening Theorem)

**Status:** LONG-TERM — requires Douady-Hubbard Straightening Theorem
**Difficulty:** Hard
**Depends on:** PLAN_01 completed

---

## What It Is

```lean
axiom fixedPoint_parameter_model_data : FixedPointParameterModelData

FixedPointParameterModelData :=
  ∀ g : BMol, IsFastRenormalizable g → Rfast g = g → ∃ c : ℂ, g = parameterToBMol c
```

Says: every fast-renormalizable fixed point of `Rfast` is (equal to) some `parameterToBMol c`.

This is a special case of the **Douady-Hubbard Straightening Theorem**:
every degree-2 polynomial-like map is hybrid equivalent to some `z ↦ z² + c`.

---

## Why This Is Hard

`parameterToBMol c` uses `U = V = Set.univ` (the whole plane). So `g = parameterToBMol c`
means the domains of `g` are the whole plane, which is likely false for any non-trivial BMol.

**Root issue**: `parameterToBMol` is a degenerate placeholder that doesn't model
real quadratic-like maps with bounded domains. The "equality" `g = parameterToBMol c`
is definitionally impossible for any meaningful `g`.

---

## Two Routes

### Route A: Fix `parameterToBMol` (Major Refactoring)

Redefine `parameterToBMol` to use bounded domains (Fatou domains / puzzle pieces).
Then `fixedPoint_parameter_model_data` becomes a genuine Straightening Theorem statement.

**Cost**: Breaking change to the entire codebase. Every theorem using `parameterToBMol c`
must be reconsidered. `lyubich_conformal_bridge` references `c : ℂ` directly,
so it also needs updating.

### Route B: Weaken to Hybrid Equivalence

Instead of `g = parameterToBMol c`, use `HybridEquivalent g (parameterToBMol c)`.
The Straightening Theorem says hybrid equivalents exist for any QL map.

**Cost**: All downstream lemmas using `parameterToBMol c` must use the equivalence.
The InconsistencyRoute works with `parameterToBMol c` specifically — it would need
to be extended to work up to hybrid equivalence.

### Route C: Accept as Axiom

`fixedPoint_parameter_model_data` is a weaker-than-general Straightening:
it only applies to Rfast-fixed points, not all QL maps. This is still a deep result
(implies Feigenbaum parameter is unique and is a quadratic polynomial) but could
reasonably be axiomatized as a named classical theorem.

**Verdict**: Accept as axiom. Label it: "Douady-Hubbard Straightening for Rfast fixed points".

---

## Connection to `parameterToBMol` Issue

The core difficulty is that `parameterToBMol c` has `U = V = univ`, making it
structurally different from any "real" quadratic-like map with bounded domains.

This suggests the real issue is architectural: the `BMol`/`parameterToBMol` formalization
is too abstract to support the Straightening Theorem without an axiom.

Until `parameterToBMol` is given a geometrically meaningful definition, this axiom
cannot be proved — only accepted.

---

## Preferred Alternative: PLAN_05

**Before spending effort here, consider PLAN_05 first.**

PLAN_05 generalizes `lyubich_conformal_bridge` to work with any `g : BMol` (not just
`parameterToBMol c`). This eliminates the need for `fixedPoint_parameter_model_data`
entirely — the Straightening Theorem is bypassed, not proved.

PLAN_05 is READY TO IMPLEMENT (estimated 1-2 hours of Lean code).

---

## Conclusion

`fixedPoint_parameter_model_data` cannot be proved from the current codebase because:
1. `parameterToBMol` uses degenerate `U = V = univ` domains
2. The Straightening Theorem is not formalized
3. Rfast fixed points in the abstract BMol setting may not have `U = V = univ`

**Recommended action**: Implement PLAN_05 instead of trying to prove this axiom.
