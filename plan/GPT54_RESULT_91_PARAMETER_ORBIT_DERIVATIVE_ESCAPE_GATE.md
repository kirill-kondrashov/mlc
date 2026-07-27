# GPT-5.4 Result 91 — Parameter orbit derivative escape gate

## Outcome

Prompt 91 is currently **blocked at the escape-transition step**.

I found the existing parameter differentiability API and the exact orbit
recurrence needed to set up the derivative recursion, but I did **not** find a
checked algebraic argument in the current library that proves

```lean
deriv (fun p : ℂ => orbit p 0 (n + 1)) c ≠ 0
```

from the sole hypothesis

```lean
2 < ‖orbit c 0 (n + 1)‖.
```

Per instructions, I made no speculative Lean source edits and did not attempt
finite filled-level connectedness or any polynomial lemniscate theorem.

## Existing checked ingredients

### 1. Parameter differentiability already exists

`Mlc/ParameterEscapeExhaustion.lean` contains

```lean
lemma differentiable_orbit_zero_param (n : ℕ) :
    Differentiable ℂ (fun c : ℂ => orbit c 0 n)
```

obtained from

```lean
differentiable_iterate_param (0 : ℂ) n
```

in `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`.

So the map

```lean
P_n(c) := orbit c 0 (n + 1)
```

is already known to be holomorphic / differentiable in `c`.

### 2. The orbit recurrence is already available

Using `orbit_succ`, one has exactly

```lean
P_{n+1}(c) = (P_n(c))^2 + c.
```

This is the right starting point for a derivative recurrence.

### 3. The escape monotonicity theorem already proved is only for orbit values

The repo already proves monotonicity of the **norms of orbit values** once they
are outside radius `2` or `R c`; e.g. in `ParameterEscapeExhaustion.lean`

```lean
parameterEscapeLevel_mono
```

shows

```lean
2 < ‖orbit c 0 (n + 1)‖ → 2 < ‖orbit c 0 (n + 2)‖.
```

But this is a statement about the orbit values themselves, not about the
parameter derivative.

## The formal derivative recurrence that should be isolated

If one sets

```lean
P_n(c) := orbit c 0 (n + 1),
D_n(c) := deriv (fun p : ℂ => orbit p 0 (n + 1)) c,
```

then differentiating

```lean
P_{n+1}(c) = (P_n(c))^2 + c
```

formally gives

```lean
D_{n+1}(c) = 2 * P_n(c) * D_n(c) + 1.
```

This is the correct recurrence. It is compatible with the local API, and one
could equally phrase it with `HasDerivAt` instead of `deriv`.

## Where the induction stalls

A natural induction trying to prove

```lean
2 < ‖P_n(c)‖ → D_n(c) ≠ 0
```

runs into the exact transition requested in the prompt:

- previous orbit value satisfies `‖P_n(c)‖ ≤ 2`,
- next orbit value satisfies `2 < ‖P_{n+1}(c)‖`.

From the derivative recurrence alone,

```lean
D_{n+1}(c) = 2 * P_n(c) * D_n(c) + 1,
```

there is no immediate contradiction if `D_{n+1}(c) = 0`, because that would
only imply

```lean
2 * P_n(c) * D_n(c) = -1.
```

Without a prior lower/upper bound on `D_n(c)`, this identity is compatible with
`‖P_n(c)‖ ≤ 2`.

So the derivative recurrence by itself does **not** force nonvanishing at the
first escaping step.

## Exact blocked statement

The first missing theorem is essentially a statement of the following form:

```lean
lemma deriv_parameterOrbit_ne_zero_of_first_escape_step
    (n : ℕ) (c : ℂ)
    (hprev : ‖orbit c 0 (n + 1)‖ ≤ 2)
    (hnext : 2 < ‖orbit c 0 (n + 2)‖) :
    deriv (fun p : ℂ => orbit p 0 (n + 2)) c ≠ 0
```

or an equivalent `HasDerivAt` formulation.

This is the exact transition singled out by Prompt 91, and I do not see a proof
of it from the currently checked algebraic API alone.

## Why it does not follow from the preceding recurrence

The recurrence

```lean
D_{n+1} = 2 P_n D_n + 1
```

is purely algebraic. To deduce `D_{n+1} ≠ 0`, one would need some additional
control on the product `P_n D_n`.

But the currently audited files provide:

- differentiability of `c ↦ orbit c 0 n`,
- continuity of `c ↦ orbit c 0 n`,
- escape-growth for the orbit values,
- connectedness of open escape superlevels,

and **not** a quantitative estimate on the parameter derivative `D_n`, nor a
structural theorem identifying critical points/critical values of the parameter
orbit polynomials.

Thus the missing ingredient is not the formal derivative recurrence itself; it
is a new estimate or structural theorem controlling parameter critical points at
the first escape step.

## Consequence for the desired contrapositive

Because the forward theorem is blocked,

```lean
deriv (fun p : ℂ => orbit p 0 (n + 1)) c = 0 →
  ‖orbit c 0 (n + 1)‖ ≤ 2
```

is also currently blocked.

## Honest conclusion

Prompt 91 should currently be recorded as a **blocker result**:

- the differentiability and recurrence setup is available;
- the crucial first-escape derivative nonvanishing statement is not justified by
  the present algebraic API;
- no Lean implementation should be added until that missing estimate/structure
  theorem is identified.

## Files audited

- `plan/GPT54_PROMPT_91_PARAMETER_ORBIT_DERIVATIVE_ESCAPE_GATE.md`
- `plan/GPT54_TASK_91_PARAMETER_ORBIT_DERIVATIVE_ESCAPE_GATE.md`
- `Mlc/ParameterEscapeExhaustion.lean`
- `Mlc/BasinConnected.lean`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`

## No code changes

I made no Lean source edits. This result records the exact derivative-gate
blocker and why it does not yet follow from the checked recurrence alone.