# TASK 53 — Separate open parameter windows from connectedness loci

## Global context

The target remains removal of:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The recommended route is genuine moving parameter geometry:

```text
open parameter window/component
→ relative intersection with MandelbrotSet
→ connected local-connectivity neighborhoods
→ migrate consumers
→ remove frozen straddling axiom
```

Result 52 defined:

```lean
connectednessLocusParameterPiece F n
```

as the connectedness locus of a moving `BMolParameterFamily`. That definition
is mathematically honest, but it is not generally open. The current generic
consumer interface `ParameterPieceLcAtData` demands openness of the pieces, so
using the connectedness locus itself as the neighborhood family is a category
error.

## Deliverable

Correct the API in `Mlc/LcAtOfShrink.lean` or a focused new module.

Introduce a two-layer family abstraction with:

```lean
window : ℕ → Set ℂ
locus  : ℕ → Set ℂ
```

and explicit relations such as:

```lean
locus n ⊆ window n
IsOpen (window n)
```

The local-connectivity consumer must use `window n` as the open neighborhood
piece and require connectedness of:

```lean
window n ∩ MandelbrotSet
```

The connectedness locus should remain available as the moving-family source
object, but it must not be forced to satisfy `IsOpen`.

Provide:

1. the corrected data structure/adapter;
2. a generic local-connectivity theorem using the open `window` family;
3. clean lemmas connecting a future connectedness-locus theorem to the relative
   connectedness field;
4. compatibility with existing frozen `ParaPuzzlePieceAt` consumers where
   possible.

Do not attempt to prove the deep window/locus topology. Make missing facts
explicit hypotheses rather than fabricating them.

## Constraints

- No frozen Green-set definition for the new moving abstraction.
- No exact-image or connectedness-witness definition of the window.
- Do not claim the current `AnalyticQuadraticLikeFamilyCore` provides a genuine
  proper unfolded equipped window.
- No `sorry`, `admit`, or new axiom.
- Do not modify the frontier axiom.
- Do not edit unrelated Böttcher modules or commit.

## Verification

Run:

```bash
lake env lean Mlc/LcAtOfShrink.lean
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_53_SEPARATE_OPEN_WINDOW_FROM_CONNECTEDNESS_LOCUS.md`

Report the corrected interface, generic theorem, compatibility status, and the
remaining concrete moving-window theorem needed for actual axiom removal.
