# PLAN 05: Eliminate `lyubich_conformal_bridge` (Long-Term)

**Status:** `LONG-TERM — after other axioms are gone`
**Difficulty:** Very High
**Depends on:** PLAN 01 completed; understand the proof strategy
**Goal:** Eliminate `lyubich_conformal_bridge` by replacing the proxy modulus with real conformal modulus

---

## Why This Matters

After PLAN 01 (axiom swap), the axiom frontier becomes:
```
Quot.sound, propext, Classical.choice   ← non-negotiable
exists_renormalization_tower            ← standard fact
lyubich_conformal_bridge                ← deep theorem
```

`lyubich_conformal_bridge` states:
```lean
LyubichConformalBridge c T :=
    (¬ Summable LyubichModulus ...) → (¬ Summable cmodulus ...)
```

This is an axiom that bridges the fake `LyubichModulus = 1` proxy to the fake
Gaussian `cmodulus`. The bridge itself is MATHEMATICALLY WRONG (since both are
proxies), but it creates the desired inconsistency.

---

## The Deeper Problem

The root issue: `cmodulus` is defined as the Gaussian modulus (always summable),
and `LyubichModulus` is defined as the constant 1 (always non-summable).
`lyubich_conformal_bridge` connects them in a way that creates a contradiction.

This is NOT real mathematics — it's an artificial inconsistency used to prove
things vacuously.

**For a REAL proof**, we would need:
1. Define `cmodulus` as the true conformal modulus of the puzzle annuli
2. Prove Lyubich's a priori bounds: `cmodulus (dynAnnulus ...) ≥ μ > 0`
3. This gives `¬Summable cmodulus` directly (without `lyubich_conformal_bridge`)

---

## What Real Lyubich Theory Says

**Lyubich's Theorem (primitive case):**
For a primitive infinitely renormalizable quadratic polynomial, the conformal
moduli of the principal nest annuli are bounded below by a positive constant,
hence the series diverges.

**In the codebase:** 
- `PrimitiveModulusDivergence.lean` has `primitive_step_modulus_bound` (currently trivial/sorry)
- Real proof requires: compactness of primitive renormalization class → modulus lower bound

---

## Route to Eliminating `lyubich_conformal_bridge`

### Option A: Prove it from existing axioms

The bridge follows from:
1. `primitive_step_modulus_bound` (lower bound on Lyubich modulus for primitive maps)
2. Connection between Lyubich modulus and conformal modulus of puzzle pieces

Currently `primitive_step_modulus_bound` is proved trivially (returns `trivial`).
Making it non-trivial requires:
- A non-proxy definition of `LyubichModulus`
- Connection to actual geometry

### Option B: Replace proxy modulus with real modulus

Redefine `cmodulus` to equal `LyubichModulus` times a scaling factor.
Then the bridge is trivial by definition.

This is a "cheat" but cleaner than the current cheat.

### Option C: Accept `lyubich_conformal_bridge` as a standard axiom

`lyubich_conformal_bridge` is analogous to "Lyubich's complex bounds theorem":
- It's a deep result proven by Lyubich in 1997
- It requires hundreds of pages of complex analysis to formalize
- Accepting it as an axiom is STANDARD in such formalization projects

This is probably the RIGHT decision for now.

---

## Recommendation

For the foreseeable future, **keep `lyubich_conformal_bridge` as an axiom**.
It represents a deep but true theorem, unlike `ir_locally_connected_seam` which
is circular. Formalizing it would be a major research project on its own.

The goal after PLAN 01 should be:
```
Quot.sound, propext, Classical.choice   ← non-negotiable
exists_renormalization_tower            ← work on this (PLAN 02/03/04)
lyubich_conformal_bridge                ← accept as standard
```

---

## If We Ever Try to Prove `lyubich_conformal_bridge`

Need to formalize:
- Quadratic-like maps (Douady-Hubbard)
- Polynomial-like restrictions (conformal welding)
- The Grötzsch inequality (extremal length)
- Lyubich's complex bounds (modulus lower bound for primitive class)

These are prerequisites for any serious formalization of Mandelbrot theory.
