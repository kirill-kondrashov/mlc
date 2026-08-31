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

# Completed -- do not rerun

Result 88 corrected the exterior topology. A follow-up constructor audit found
that `GenuineBottcherNearInfinityParameterExtensionData` is not an available
near-infinity upgrade: its `global` field already assumes the missing
`GenuineBottcherLocalParameterFamilyData`.

Do not attempt to package that contract as the next step. The no-new-axiom
foundation sequence next establishes connectedness of `MandelbrotSet` itself,
rather than using the existing `mandelbrot_set_connected` axiom. This is a
necessary topology gate for an exterior-uniformization route; it does not by
itself construct the coordinate.

Continue with:

`plan/GPT54_PROMPT_89_FINITE_PARAMETER_FILLED_LEVEL_CONNECTIVITY_GATE.md`
