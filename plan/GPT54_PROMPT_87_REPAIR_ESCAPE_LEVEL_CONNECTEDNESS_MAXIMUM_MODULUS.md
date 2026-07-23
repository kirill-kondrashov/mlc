Repair the premature blocker in Result 84:

`plan/GPT54_TASK_87_REPAIR_ESCAPE_LEVEL_CONNECTEDNESS_MAXIMUM_MODULUS.md`

Do **not** pursue the critical-value / general polynomial-lemniscate route
from Prompt 84. It is unnecessarily strong. The repository already contains
the applicable maximum-modulus separation proof in
`Mlc/BasinConnected.lean`, especially:

- `maxmod_absurd`;
- `frontier_side_subset_compl`;
- `exterior_preconnected`;
- `isPreconnected_orbit_superlevel`.

That proof establishes preconnectedness of a norm superlevel from:

1. an entire (globally differentiable) map;
2. a connected exterior `{z | r < ‖z‖}` contained in the superlevel;
3. the maximum-modulus contradiction excluding a bounded separated side.

Apply or extract that argument for the parameter map

```lean
fun c : ℂ => orbit c 0 (n + 1)
```

and radius `2`.

Required checked results:

```lean
theorem isPreconnected_parameterEscapeLevel (n : ℕ) :
  IsPreconnected (ParameterEscapeLevel n)

theorem parameterEscapeLevel_isConnected (n : ℕ) :
  IsConnected (ParameterEscapeLevel n)
```

Prove the prerequisites rather than assuming them:

1. Establish global differentiability of
   `c ↦ orbit c 0 (n + 1)`, preferably by the same elementary induction as
   `continuous_orbit_zero_param`, or by a directly applicable existing theorem.
2. Establish
   `{c | 2 < ‖c‖} ⊆ ParameterEscapeLevel n` from
   `ParameterEscapeLevel 0` and repeated
   `parameterEscapeLevel_mono`.
3. Reuse the exterior preconnectedness and maximum-modulus helpers. Since
   `R (0 : ℂ) = 2`, specialize existing helpers at `0` if that produces the
   cleanest proof; otherwise extract a small generic radius-`r` helper from
   `BasinConnected.lean` and reuse it there as well.
4. Supply nonemptiness from the exterior subset to upgrade preconnectedness to
   connectedness.

Do not duplicate a competing large separation proof if a small extraction from
`BasinConnected.lean` gives a reusable theorem. Do not use
`mandelbrot_set_connected`, a generic full-compact-complement theorem,
critical-value hypotheses, a parameter coordinate, `external_ray_map_exists`,
the frozen straddling axiom, a Riemann map, a new axiom, `sorry`, or `admit`.
Do not commit.

Validate the edited module, full build, and root axiom check.

Write:

`plan/GPT54_RESULT_87_REPAIR_ESCAPE_LEVEL_CONNECTEDNESS_MAXIMUM_MODULUS.md`
