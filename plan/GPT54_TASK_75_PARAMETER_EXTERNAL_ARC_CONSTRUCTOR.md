# TASK 75 — Construct a genuine parameter external arc

## Objective

Populate the completed finite graph model with the first actual
parameter-plane boundary arc.

Target an arc:

```lean
γ : Set.Icc (0 : ℝ) 1 → ℂ
```

with proved continuity, injectivity, and exterior membership
`γ t ∉ MandelbrotSet`, plus endpoint/level information if available.

## Source audit

Inspect all project declarations for:

- a parameter-plane Böttcher/external coordinate;
- parameter Green/equipotential maps;
- external parameter rays;
- ray landing/endpoints;
- an equivalent theorem producing finite arcs in
  `MandelbrotSetᶜ`.

Dynamical-plane ray maps do not count unless a proved parameter-plane
identification is supplied.

## Action

If a genuine parameter source exists, implement the smallest
`BoundaryArc` constructor and validate it.

If it does not exist, make no source edits. Report the exact missing theorem,
likely a parameter exterior coordinate/homeomorphism or an equivalent
parameter-ray segment theorem.

## Constraints

- no frontier axiom;
- no frozen para-puzzle alias;
- no fake coordinate or identity map;
- no new axiom, `sorry`, or `admit`;
- no phase–parameter or Mandelbrot-slice claim yet;
- do not commit.

## Result

Write:

`plan/GPT54_RESULT_75_PARAMETER_EXTERNAL_ARC_CONSTRUCTOR.md`
