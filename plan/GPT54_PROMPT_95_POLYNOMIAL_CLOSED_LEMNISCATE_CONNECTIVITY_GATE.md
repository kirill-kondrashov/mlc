# Gated -- run only after Result 94 proves critical-value containment

`plan/GPT54_TASK_95_POLYNOMIAL_CLOSED_LEMNISCATE_CONNECTIVITY_GATE.md`

Given a checked theorem that every critical value of
`ParameterOrbitPolynomial n` lies in `Metric.closedBall (0 : ℂ) 2`, prove or
precisely source the required closed-lemniscate theorem:

```lean
IsConnected {c : ℂ | ‖(ParameterOrbitPolynomial n).eval c‖ ≤ 2}.
```

The theorem must be noncircular and must not use
`mandelbrot_set_connected`, finite filled-level connectedness, a parameter
Böttcher coordinate, external rays, Riemann--Hurwitz as an assumed black box,
new axioms, `sorry`, or `admit`. Reuse `Mlc/FilledJuliaConnected.lean` only
where its hypotheses genuinely match the polynomial-preimage setting.

If the necessary proper-map, covering, or planar topology theorem is absent,
record its exact Lean-facing statement rather than adding an interface
contract. Do not commit.

Write:

`plan/GPT54_RESULT_95_POLYNOMIAL_CLOSED_LEMNISCATE_CONNECTIVITY_GATE.md`
