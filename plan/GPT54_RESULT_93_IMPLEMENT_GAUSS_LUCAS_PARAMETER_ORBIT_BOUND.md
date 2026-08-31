# GPT-5.4 Result 93 — Implement Gauss–Lucas parameter-orbit bound

## Outcome

Implemented a checked partial result in `Mlc/ParameterOrbitPolynomial.lean`.

### New definitions and lemmas
- `ParameterOrbitPolynomial : ℕ → ℂ[X]`
- `parameterOrbitPolynomial_natDegree`
- `parameterOrbitPolynomial_nonzero`
- `parameterOrbitPolynomial_eval`
- `parameterOrbitPolynomial_rootSet_subset_mandelbrotSet`
- `parameterOrbitPolynomial_rootSet_subset_closedBall_two`
- `parameterOrbitPolynomial_derivative_root_norm_le_two`

## What is proved

For the recursively defined parameter polynomial
`P₀(X)=X`, `P_{n+1}(X)=P_n(X)^2 + X`, we now have:

1. `P_n(c) = orbit c 0 (n + 1)`.
2. Every root of `P_n` lies in `MandelbrotSet`, using the newly available checked lemma
   `mandelbrot_of_orbit_zero` from `Mlc/ParameterEscapeExhaustion.lean`.
3. Hence every root of `P_n` lies in the closed ball `Metric.closedBall (0 : ℂ) 2`.
4. By mathlib's Gauss–Lucas theorem,
   every root of `P_n.derivative` lies in the convex hull of the roots of `P_n`, so in the
   same radius-2 closed ball.
5. Therefore:
   `parameterOrbitPolynomial_derivative_root_norm_le_two`.

## Exact frontier moved

This discharges the main implementation request from Prompt 93: the checked critical-point
location theorem for the parameter-orbit polynomial is now in source.

## Honesty / scope

This does **not** prove any stronger escape-derivative theorem, and does **not** resolve the
first-escape obstruction noted in Result 91. It is exactly a Gauss–Lucas critical-point bound.
