# GPT-5.4 Result 84 — Finite Escape Lemniscate Connectivity Gate

## Outcome

Prompt 84 is **blocked at the finite polynomial lemniscate theorem** needed to prove

```lean
theorem parameterEscapeLevel_isConnected (n : ℕ) :
  IsConnected (ParameterEscapeLevel n)
```

for

```lean
def ParameterEscapeLevel (n : ℕ) : Set ℂ :=
  {c : ℂ | 2 < ‖orbit c 0 (n + 1)‖}
```

I audited the current repository and Mathlib-facing local infrastructure carefully enough to identify the first exact missing bridge. I did **not** make speculative Lean source edits.

## What is already available

### 1. The finite escape levels themselves
`Mlc/ParameterEscapeExhaustion.lean` already provides the checked package:

- `ParameterEscapeLevel`
- `isOpen_parameterEscapeLevel`
- `parameterEscapeLevel_mono`
- `not_mandelbrot_of_mem_parameterEscapeLevel`
- `compl_mandelbrot_eq_iUnion_parameterEscapeLevel`

So Prompt 84 is not about exhaustion anymore; it is specifically about **finite-level connectedness**.

### 2. The parameter iterate is holomorphic/polynomial in `c`
The file `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean` contains

```lean
lemma differentiable_iterate_param (z : ℂ) (n : ℕ) :
    Differentiable ℂ (fun c : ℂ => (quadratic_map c)^[n] z)
```

with the explicit inductive formula

```lean
f_c^{n+1}(z) = (f_c^n(z))^2 + c.
```

So for fixed `z = 0`, the map

```lean
c ↦ orbit c 0 (n + 1)
```

is already known to be holomorphic; mathematically it is a polynomial in `c`.

### 3. Properness for the basic quadratic map
`Mlc/RenormalizationTypes.lean` proves:

```lean
lemma isProperMap_pow2 : IsProperMap (fun z : ℂ => z^2)
lemma isProperMap_quadratic (c : ℂ) : IsProperMap (fun z : ℂ => z^2 + c)
```

and `Mlc/FilledJuliaConnected.lean` shows a successful pattern for using properness plus closed-map arguments in a **very special quadratic preimage** setting.

## What I checked and why it does not yet close Prompt 84

### Base level sanity check
For `n = 0`,

```lean
ParameterEscapeLevel 0 = {c : ℂ | 2 < ‖c‖},
```

which is connected in `ℂ`.

So the statement is true at the first level and is not vacuous.

### Why `FilledJuliaConnected.lean` does not directly transfer
`Mlc/FilledJuliaConnected.lean` proves connectedness of certain preimages by the special map

```lean
z ↦ z^2 + c
```

using a special structural fact: after translating by `-c`, one reduces to the squaring map, and for squaring there is a concrete involution argument `z ↦ -z` plus square-root lifting. This is encoded in:

- `isPreconnected_sq_preimage`
- `isPreconnected_quadratic_preimage`

That argument is **specific to quadratic dynamical preimages**. It does not supply the needed theorem for the arbitrary finite parameter polynomial

```lean
P_n(c) := orbit c 0 (n + 1).
```

For general `n`, Prompt 84 would require a theorem about the superlevel lemniscate

```lean
{c : ℂ | 2 < ‖P_n(c)‖}.
```

Nothing in the current repo upgrades the quadratic preimage argument to a general polynomial lemniscate statement.

## The first exact missing theorem

The first missing ingredient is a genuine theorem of the following shape (or an equivalent replacement):

```lean
lemma isConnected_norm_gt_of_polynomial_criticalValues_bounded
    (P : Polynomial ℂ)
    (hdeg : 1 ≤ P.natDegree)
    (hcrit : ∀ z, Polynomial.eval (Polynomial.derivative P) z = 0 →
      ‖Polynomial.eval P z‖ ≤ 2) :
    IsConnected {w : ℂ | 2 < ‖Polynomial.eval w P‖}
```

More invariantly: a polynomial lemniscate / preimage-of-exterior theorem saying that if all critical values of a nonconstant complex polynomial lie in the closed disk `closedBall 0 2`, then the exterior preimage

```lean
P ⁻¹' {w : ℂ | 2 < ‖w‖}
```

is connected.

This is the exact classical bridge Prompt 84 asks for.

## What is missing even before the application to `P_n`

To apply such a theorem to

```lean
P_n(c) = orbit c 0 (n + 1),
```

the current repo would still need a checked theorem identifying or controlling the critical values of `P_n`. I found no existing source theorem that states:

- the critical points of `c ↦ orbit c 0 (n + 1)`;
- that their images lie in `‖·‖ ≤ 2`;
- or a polynomial covering theorem that bypasses explicit critical-value analysis.

So there are really two layers:

1. **general polynomial lemniscate connectivity theorem** — missing;
2. **critical-value containment for the finite parameter polynomial `P_n`** — also missing.

The first is the earliest exact blocker.

## Honest conclusion

Prompt 84 cannot honestly be completed from the present repository by a small local patch.

The existing checked infrastructure is enough to define and exhaust the finite escape levels, and enough to show the parameter iterates are holomorphic in `c`, but it does **not** yet contain the general planar topology / polynomial lemniscate theorem needed to deduce that each finite superlevel set is connected.

I therefore made **no source edits** for this prompt and recorded the blocker here rather than faking a theorem or smuggling in a new axiom.

## Suggested next honest step

The next theorem to source/prove is a standalone polynomial result of the form:

- connectedness of the exterior lemniscate of a nonconstant complex polynomial when all critical values lie in a closed disk;

or, if Mathlib already has enough proper-map and local-homeomorphism API, a formal covering-space version specialized to

```lean
ℂ \ P⁻¹(closedBall 0 2).
```

Only after that should one return to the specific parameter polynomial `P_n(c) = orbit c 0 (n + 1)`.
