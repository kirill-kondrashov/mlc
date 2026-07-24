Correct the parameter-exterior target before attempting another construction:

`plan/GPT54_TASK_88_CORRECT_EXTERIOR_UNIFORMIZATION_TARGET.md`

Result 85 now proves:

```lean
IsConnected (MandelbrotSetᶜ)
```

Do not try to strengthen this to ordinary
`IsSimplyConnected (MandelbrotSetᶜ)`: the exterior unit disk
`{w : ℂ | 1 < ‖w‖}` is itself not simply connected as a subspace of `ℂ`.
The prior Prompts 77--82 and 80 therefore used the wrong topology for an
exterior coordinate.

This is a specification/source audit. Determine the exact Lean-facing target
for the correct theorem:

- an exterior conformal equivalence between `MandelbrotSetᶜ` and
  `{w : ℂ | 1 < ‖w‖}`, normalized at infinity; or
- an equivalent spherical/one-point-compactified uniformization statement; or
- a direct parameter Böttcher theorem
  `Φ(c) = φ_c(c)` on `MandelbrotSetᶜ` with the required holomorphic,
  injective, surjective, and infinity-normalization conclusions.

Audit the existing code with particular attention to:

- `Mlc/ParameterEscapeExhaustion.lean`;
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`;
- `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`;
- `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`;
- current theorem-facing parameter-coordinate packages.

Identify the smallest genuine non-axiomatic source theorem needed next and
whether the checked finite escape exhaustion supplies any part of its domain,
continuation, or monodromy argument. Do not use
`mandelbrot_set_connected`: it is an existing axiom and would enlarge the
final no-new-axiom frontier. Do not use `external_ray_map_exists`, a generic
ordinary-plane Riemann-map theorem, the frozen straddling axiom, placeholder
coordinates, new axioms, `sorry`, or `admit`.

Do not edit Lean source unless a small target definition is clearly necessary
and non-duplicative. Do not commit.

Write:

`plan/GPT54_RESULT_88_CORRECT_EXTERIOR_UNIFORMIZATION_TARGET.md`
