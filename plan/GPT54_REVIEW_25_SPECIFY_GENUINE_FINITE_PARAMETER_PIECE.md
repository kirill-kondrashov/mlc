# Supervisor Review 25: Genuine finite-level parameter piece specification

**Verdict:** rejected; the active task was not completed.

Task 25 explicitly suspended the renormalization/tube sequence and requested one
finite-level moving-parameter parapuzzle object defined from parameter geometry.
Result 25 instead returns to `M(g)` / `M°`, the same renormalization-locus route
that was suspended after the user redirected work to the green-sublevel frontier.

The proposed object fails the task's required finite-level consumer tests:

- no `ParameterGraph(base, depth)` is actually defined;
- no parameter rays or equipotential boundary are specified;
- one little Mandelbrot copy is not a relative open neighborhood of the base;
- Theorems 10.1 and 10.15 do not supply depth-indexed antitone nesting;
- they do not supply singleton intersection/shrinkage;
- they do not identify or eliminate the frozen Green-sublevel target.

The compile-tested structure

```lean
connected_inter_mandelbrot : ... IsConnected (...)
```

stores the exact desired conclusion as a field. This is connectivity packaging,
not a geometric construction, and is forbidden by the active plan's Phase 0
guardrail. Likewise, a generic `LcAtOfShrink` interface may eventually improve
software structure, but implementing it before fixing a concrete geometric object
does not advance the frontier.

The next task must not mention `M(g)`, `M°`, straightening, or renormalization
windows as its selected object. It must either:

1. pin an exact finite parameter graph/component from moving parameter rays and
   equipotentials, with a concrete source definition; or
2. conclude that the immediate blocker is the absence of parameter-ray /
   parameter-equipotential foundations and specify that layer precisely.

No abstract connectedness field is acceptable.
