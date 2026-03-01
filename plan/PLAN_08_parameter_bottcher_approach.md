# PLAN 08: Parameter Böttcher Coordinate Approach

**Status:** `░░░░░░░░░░` **0%**
**State:** `PROPOSED`
**Difficulty:** Medium-High
**Risk:** Medium — well-understood mathematically, requires new formalization.

## Core Idea

Instead of using the Böttcher coordinate of individual polynomials f_c
(the dynamical Böttcher map, which has the wrong definition in the codebase),
use the **parameter-space Böttcher coordinate** Φ_M : ℂ\M → {|w| > 1}.

This is the uniformization of the complement of the Mandelbrot set:
```
Φ_M(c) = φ_c(c)
```
where φ_c is the (true) dynamical Böttcher coordinate of z² + c.

MLC is equivalent to Φ_M extending continuously to ∂M. This is a completely
different approach from the dynamical Böttcher map in the codebase.

## Why This Might Unstick Us

1. The parameter Böttcher coordinate Φ_M is WELL-DEFINED (doesn't have the
   angle error of the crude dynamical `bottcher_map`, because Φ_M is
   classically defined using the true φ_c)

2. Φ_M has a simple explicit formula:
   ```
   Φ_M(c) = lim_{n→∞} (f_c^n(c))^{1/2^n} = lim_{n→∞} c_n^{1/2^n}
   ```
   where c_0 = c, c_{n+1} = c_n² + c (the critical orbit)

3. MLC ⟺ Φ_M extends to a continuous surjection ∂M → S¹

4. This approach completely bypasses the dynamical `bottcher_map` and its
   crude definition. We'd define Φ_M from scratch using the critical orbit.

## Implementation Steps

### Step 1: Define the parameter Böttcher sequence

```lean
noncomputable def mandelbrot_bottcher_seq (c : ℂ) (n : ℕ) : ℂ :=
  ((quadratic_map c)^[n] c) ^ ((1 : ℂ) / 2 ^ n)
```

(Note: this is the critical orbit `c_n = f_c^n(c)` raised to `1/2^n`.)

### Step 2: Prove convergence for c ∉ M

For c outside M, the critical orbit escapes: `|c_n| → ∞`. The sequence
`c_n^{1/2^n}` converges to the parameter Böttcher coordinate Φ_M(c).

Standard estimate: `|Φ_M(c)| = exp(G_M(c))` where G_M is the parameter
Green function (= G(c, c), the dynamical Green function evaluated at the
critical value).

### Step 3: Define the parameter Böttcher coordinate

```lean
noncomputable def param_bottcher (c : ℂ) : ℂ :=
  limUnder atTop (mandelbrot_bottcher_seq c)
```

### Step 4: Prove key properties

- `|param_bottcher c| = exp(G(c, c))` for c ∉ M
- `param_bottcher` is holomorphic on ℂ\M
- `param_bottcher` maps ℂ\M biholomorphically onto {|w| > 1}
- `param_bottcher(c)/c → 1` as c → ∞

### Step 5: Formulate MLC in terms of Φ_M

MLC is equivalent to:
```lean
ContinuousOn param_bottcher_extended (Set.univ : Set ℂ)
```
where `param_bottcher_extended` is the continuous extension of `param_bottcher`
from ℂ\M to ℂ. Or equivalently:
```lean
∀ c ∈ ∂M, ∃ L, Tendsto param_bottcher (𝓝[ℂ\M] c) (𝓝 L)
```

### Step 6: Prove the equivalence

```lean
theorem mlc_iff_param_bottcher_extends :
    LocallyConnectedSpace mandelbrotSet ↔
    ContinuousOn param_bottcher_extended univ
```

This is the Douady-Hubbard theorem: MLC ⟺ parameter rays land.

### Step 7: Prove parameter ray landing

For each angle θ, the parameter ray at angle θ:
```
R_θ = {Φ_M⁻¹(r · e^{2πiθ}) : r > 1}
```
lands at a point of ∂M.

This is the core of MLC and requires:
- Yoccoz's theorem for finitely renormalizable angles
- Renormalization theory for infinitely renormalizable angles

## Assessment

This approach is mathematically cleaner because:
1. It uses the PARAMETER Böttcher coordinate, not the dynamical one
2. The parameter Böttcher coordinate is correctly defined via the critical
   orbit limit (no angle error)
3. MLC has a clean equivalent formulation in terms of Φ_M

The downside is that it requires significant new formalization:
- Critical orbit limits
- Parameter Green function
- Biholomorphicity of Φ_M
- The Douady-Hubbard equivalence
- Ray landing theory

## Comparison with Other Plans

- **vs Plan 01/03** (fix dynamical bottcher_map): This plan avoids touching
  the dynamical map entirely.
- **vs Plan 02** (strategy decomposition): This is an alternative mathematical
  route to MLC that's arguably more natural.
- **vs Plan 06** (new architecture): This provides a specific mathematical
  architecture (parameter rays) rather than a general restructuring.

## Priority

Medium-High. This is a mathematically principled approach that could
provide a clean foundation for the MLC proof. However, it requires
substantial new infrastructure.
