# TASK 77 — Define fullness and exterior targets

## Goal

Specify the exact Lean and mathematical targets needed before constructing a
parameter external coordinate.

## Audit

Inspect existing definitions for:

- `MandelbrotSet`;
- compactness and connectedness;
- complements and open domains;
- `IsSimplyConnected` / `SimplyConnectedSpace`;
- conformal equivalences and normalization at infinity.

Choose or define, without duplication, the right notions of:

```lean
FullPlaneSet K
FullContinuum K
IsSimplyConnected (MandelbrotSetᶜ)
```

only if compatible with existing APIs.

Record precise sourced theorem statements for:

- Mandelbrot fullness;
- the planar full-compact-complement bridge;
- unbounded Riemann mapping.

## Constraints

- no new axiom;
- no target-shaped opaque structure;
- no external-coordinate assumption;
- no use of the frozen straddling axiom;
- no `sorry` or `admit`;
- do not commit.

## Result

Write:

`plan/GPT54_RESULT_77_DEFINE_FULLNESS_AND_EXTERIOR_TARGETS.md`
