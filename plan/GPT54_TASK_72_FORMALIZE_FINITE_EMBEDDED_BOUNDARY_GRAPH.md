# TASK 72 — Formalize finite embedded boundary graphs

## Objective

Implement the first concrete source-side foundation identified by Result 68:
finite embedded boundary graphs and their selected complementary components.

Create, preferably:

```text
Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean
```

## Model

Use a real finite geometric model, for example:

- continuous injective arcs from `Icc (0 : ℝ) 1` to `ℂ`;
- endpoint/incidence data;
- pairwise disjoint interiors or an equivalent explicit no-crossing condition;
- a carrier equal to the finite union of the arc images.

Do not use an arbitrary set with opaque topology fields as the boundary model.

## Prove

For the carrier `Γ`:

1. each arc image is compact and closed;
2. finite union `Γ` is closed;
3. `Γᶜ` is open;
4. for `z₀ ∉ Γ`, the selected window
   `connectedComponentIn Γᶜ z₀` is open and contains `z₀`;
5. carrier inclusion under graph refinement implies inclusion of selected
   basepoint components, assuming the basepoint lies in both complements;
6. package these facts for a depth-indexed refined graph family.

The component-inclusion result should use actual connectedness/component
properties, not an axiom.

## Non-goals

- no Jordan-curve or boundedness theorem unless independently proved;
- no Mandelbrot connectedness;
- no phase–parameter correspondence;
- no provider instantiation;
- no frozen frontier axiom;
- no `sorry`, `admit`, or new axiom;
- do not commit.

## Validation

Run the smallest relevant Lean checks, then:

```bash
lake build
lake env lean check_axioms.lean
```

## Result

Write:

`plan/GPT54_RESULT_72_FORMALIZE_FINITE_EMBEDDED_BOUNDARY_GRAPH.md`

If even this finite topology model cannot be implemented from existing
foundations, make no speculative edits and identify the exact missing Mathlib
lemma.
