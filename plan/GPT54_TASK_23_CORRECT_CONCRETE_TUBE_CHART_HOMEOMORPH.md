# GPT-5.4 Worker Task 23: Correct the concrete tube chart using Homeomorph

**Repository:** `/home/kir/pers/mlc`
**Mode:** read-only corrective Lean API audit
**Result file:** `plan/GPT54_RESULT_23_CORRECT_CONCRETE_TUBE_CHART_HOMEOMORPH.md`

## Safety

Write only the result report, via atomic rename. Do not edit repository sources,
dependencies, plans, or prior artifacts; do not commit. Use `/tmp` for Lean probes.

Read Result 22 and Supervisor Review 22.

## Goal

Produce a genuinely locally trivial, compile-tested project-local tube chart. The
chart must use `Homeomorph`, have the exact projection-preimage source, the full
base-times-disk target, and projection compatibility.

## A. Canonical projection

For `Λ : Set ℂ`, `total : Set (ℂ × ℂ)`, and
`hscope : total ⊆ Λ ×ˢ (univ : Set ℂ)`, define and compile-test the canonical map:

```lean
tubeProj : total → Λ
```

using the first coordinate and `hscope`. Prove its value/coercion simp lemma. Do not
store a redundant arbitrary projection in the tube once this map is available.

## B. Correct local chart

Define a chart parameterized by the canonical projection with exactly:

- `baseSet : Set Λ`;
- `isOpen_baseSet : IsOpen baseSet`;
- a homeomorphism

  ```lean
  {p : total // tubeProj hscope p ∈ baseSet} ≃ₜ
    (baseSet × DiskType model)
  ```

- a projection-compatibility law saying the first component of the image equals
  the projection of the underlying total point.

Work out and report the exact subtype coercions. The chart must not store arbitrary
`source`, `target`, `toFun`, or `invFun` fields.

Use the inherited subtype topology for disk models unless a compilation result
proves an explicit instance is needed.

## C. Atlas

Define an atlas assigning a corrected chart to every `c : Λ` and proving
`c ∈ (chartAt c).baseSet`. Compile it.

State and, where elementary, prove:

- every base point has a chart;
- projection is surjective (derive a preimage using a point of the disk model and
  the inverse homeomorphism);
- chart projection compatibility.

Be careful that both open and closed unit disk models are nonempty; give concrete
zero elements or lemmas.

## D. Fiber homeomorphism

Determine whether the chart data immediately yields a homeomorphism between the
full fiber over `c` and `DiskType model`. Give a compile-oriented theorem signature
and either compile its proof or identify the exact subtype-equivalence lemma still
needed. Do not claim the theorem merely from inverse laws.

## E. Integration

Compile-test `QuadraticLikeTube` tied directly to a core total space and a family
wrapper carrying source and target tube atlases. Avoid duplicate total/scoping
fields and all opaque local-triviality/Jordan propositions.

Do not add properness, unfolding, equipment, tubing in the later analytic sense,
straightening, or connectedness conclusions.

## F. Decision

Choose exactly one:

1. corrected concrete tube charts/atlas are ready for implementation;
2. chart and atlas compile, but projection/fiber theorems need a small preliminary
   subtype-homeomorphism lemma;
3. use Mathlib `Pretrivialization` instead because the local structure remains
   inadequate;
4. defer tube formalization.

Give the exact next worker task but do not create its file.

## Report contract

Include complete tested code, exact commands and imports, compilation results,
full `git status --short`, and confirmation that only the result artifact was
written and no commit was made.
