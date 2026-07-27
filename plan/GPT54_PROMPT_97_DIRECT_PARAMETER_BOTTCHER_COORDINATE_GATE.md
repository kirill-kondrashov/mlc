# Gated -- run only after a checked non-axiomatic Mandelbrot connectedness theorem

`plan/GPT54_TASK_97_DIRECT_PARAMETER_BOTTCHER_COORDINATE_GATE.md`

After Prompt 90 proves `IsConnected MandelbrotSet` without its axiom, construct
or isolate the exact missing source theorem for a normalized exterior
coordinate:

```lean
Φ : MandelbrotSetᶜ → {w : ℂ | 1 < ‖w‖}.
```

The theorem must be a direct parameter Böttcher or equivalent spherical
exterior-uniformization theorem. Do not claim ordinary
`IsSimplyConnected (MandelbrotSetᶜ)`, use a generic unbounded Riemann map, or
evaluate the near-infinity series at `z = c`. Connectedness alone does not
resolve monodromy.

No use of `mandelbrot_set_connected`, `external_ray_map_exists`, the frozen
straddling axiom, new axioms, `sorry`, `admit`, or opaque continuation
contracts. Do not commit.

Write:

`plan/GPT54_RESULT_97_DIRECT_PARAMETER_BOTTCHER_COORDINATE_GATE.md`
