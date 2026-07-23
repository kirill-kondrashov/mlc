Target the exact missing analytic primitive identified by Result 74:

`plan/GPT54_TASK_75_PARAMETER_EXTERNAL_ARC_CONSTRUCTOR.md`

The finite boundary graph foundation is complete, but no actual quadratic
parameter-side ray/equipotential arc can yet populate it.

Determine whether the repository can prove a concrete finite parameter exterior
arc, for example:

```lean
∃ γ : Set.Icc (0 : ℝ) 1 → ℂ,
  Continuous γ ∧ Function.Injective γ ∧
  (∀ t, γ t ∉ MandelbrotSet)
```

with endpoints/level data sufficient to serve as one edge of a finite
parapuzzle boundary graph.

Use only a genuinely proved parameter-plane external coordinate, equipotential
map, or equivalent source theorem. Audit:

- parameter-plane Böttcher/external-coordinate declarations;
- Green/equipotential parameter maps;
- ray landing and endpoint results;
- any theorem identifying the exterior of `MandelbrotSet` with a coordinate
  domain.

If a valid source exists, implement the smallest constructor into
`BoundaryArc`, proving continuity, injectivity, exterior membership, and any
endpoint facts actually available.

If no parameter-plane source exists, make no source edits and report that the
first missing theorem is the construction of a genuine parameter external
coordinate (or an equivalent finite arc theorem). Do not substitute a
dynamical-plane ray for a parameter-plane arc.

Constraints:

- no frozen straddling axiom;
- no `ParaPuzzlePieceAt` alias;
- no placeholder or identity coordinate;
- no new axiom, `sorry`, or `admit`;
- do not claim phase–parameter transport or Mandelbrot connectedness yet;
- do not commit.

Write:

`plan/GPT54_RESULT_75_PARAMETER_EXTERNAL_ARC_CONSTRUCTOR.md`
