# GPT-5.4 Result 92 — Gauss–Lucas parameter orbit critical-point bound

## Outcome

Prompt 92 is **plausibly on the right route but currently blocked at the first
missing polynomial bridge**.

I found the checked Gauss–Lucas theorem in mathlib:

```lean
Polynomial.rootSet_derivative_subset_convexHull_rootSet
```

and the repo already has the needed disk bound

```lean
mandelbrotSet_subset_closedBall_two :
  MandelbrotSet ⊆ Metric.closedBall (0 : ℂ) 2.
```

So the intended plan is mathematically coherent. However, I did **not** find an
already-formalized bridge in the current repo showing that a root of the
parameter-orbit polynomial gives a bounded critical orbit, i.e. that

```lean
(ParameterOrbitPolynomial n).eval c = 0
```

forces `c ∈ MandelbrotSet` by turning `orbit c 0 (n + 1) = 0` into a periodic,
hence bounded, orbit.

Per instructions, I made no speculative Lean source edits.

## What is available

### 1. Gauss–Lucas is present in mathlib

In mathlib file

- `.lake/packages/mathlib/Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean`

there is the theorem

```lean
Polynomial.rootSet_derivative_subset_convexHull_rootSet
```

stating that for a nonconstant complex polynomial `P`, every root of
`P.derivative` lies in the convex hull of `P.rootSet ℂ`.

### 2. Convexity of the radius-2 disk is available

Mathlib provides

```lean
convex_closedBall (0 : ℂ) 2
```

for the closed Euclidean ball.

Hence, if one could show

```lean
(ParameterOrbitPolynomial n).rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 2,
```

then Gauss–Lucas would immediately imply the corresponding bound for the root
set of the derivative.

### 3. The parameter-side radius-2 bound is already in the repo

`Mlc/Quadratic/Complex/ParaPuzzleBasis.lean` already proves

```lean
mandelbrotSet_subset_closedBall_two :
    MandelbrotSet ⊆ Metric.closedBall (0 : ℂ) 2.
```

So it would suffice to show that every root of the parameter-orbit polynomial
belongs to `MandelbrotSet`.

### 4. The intended orbit polynomial is mathematically natural

The recursive definition requested in the prompt,

```lean
ParameterOrbitPolynomial 0 = Polynomial.X
ParameterOrbitPolynomial (n + 1) =
  (ParameterOrbitPolynomial n)^2 + Polynomial.X,
```

plainly matches the parameter critical orbit relation

```lean
orbit c 0 (n + 1).
```

I did not formalize the definition because the prompt explicitly forbids
speculative source edits when a blocker appears first.

## Exact blocker

The first exact missing theorem is a short periodic-orbit-to-Mandelbrot bridge,
for example:

```lean
lemma mandelbrot_of_orbit_zero
    (c : ℂ) (n : ℕ)
    (h : orbit c 0 (n + 1) = 0) :
    c ∈ MandelbrotSet
```

or equivalently a bounded-orbit statement:

```lean
lemma boundedOrbit_of_orbit_zero
    (c : ℂ) (n : ℕ)
    (h : orbit c 0 (n + 1) = 0) :
    boundedOrbit c 0.
```

Mathematically this should be easy: after time `n + 1`, the orbit returns to
`0`, so the future orbit repeats the initial tail and is periodic, hence bounded.
But I did not find this lemma already checked in the current repo surface.

Without that bridge, I cannot justify Step 3 of the prompt:

```lean
(ParameterOrbitPolynomial n).eval c = 0 → c ∈ MandelbrotSet.
```

## Why this is the first blocker

The later Gauss–Lucas step itself appears available once the root-set inclusion
is in hand:

1. prove `0 < degree (ParameterOrbitPolynomial n)`;
2. use
   `Polynomial.rootSet_derivative_subset_convexHull_rootSet`;
3. combine root-set inclusion into the closed ball with
   `convexHull_min` and `convex_closedBall`.

So the fundamental obstruction is earlier: getting the roots of the orbit
polynomial into `MandelbrotSet`.

## What the completed route should look like after the blocker is filled

If the missing periodic-orbit bridge is added, the rest should be straightforward:

1. define `ParameterOrbitPolynomial` recursively;
2. prove
   ```lean
   (ParameterOrbitPolynomial n).eval c = orbit c 0 (n + 1);
   ```
3. from a root, deduce `orbit c 0 (n + 1) = 0`;
4. apply `mandelbrot_of_orbit_zero` to obtain `c ∈ MandelbrotSet`;
5. apply `mandelbrotSet_subset_closedBall_two`;
6. deduce
   ```lean
   (ParameterOrbitPolynomial n).rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 2;
   ```
7. apply Gauss–Lucas and convexity of the closed ball to get
   ```lean
   (ParameterOrbitPolynomial n).derivative.eval c = 0 → ‖c‖ ≤ 2.
   ```

This would still be only a **critical-point** bound, not the missing
critical-value theorem.

## Honest conclusion

Prompt 92 should currently be recorded as a **blocker result**.

The first exact missing theorem is the boundedness/Mandelbrot membership of a
parameter whose critical orbit returns to `0`. Until that bridge is formalized,
it is premature to add the polynomial package or claim the Gauss–Lucas critical
point bound in Lean.

## Files audited

- `plan/GPT54_PROMPT_92_GAUSS_LUCAS_PARAMETER_ORBIT_CRITICAL_POINT_BOUND.md`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherCore.lean`
- `Mlc/ParaPuzzleContainment.lean`
- `.lake/packages/mathlib/Mathlib/Analysis/Complex/Polynomial/GaussLucas.lean`

## Plan note

The repo root currently has no `plan.md`, so I did not update it.

## No code changes

I made no Lean source edits. This result records the first exact blocker on the
Gauss–Lucas parameter critical-point route.