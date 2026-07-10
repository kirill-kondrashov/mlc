# GPT54 Result 02 — Formalize Carving No-Go

## Outcome

Completed successfully.

## Lean changes

Edited only `Mlc/ParaPuzzleCarvingReduction.lean` among Lean sources, as requested.
Added a sorry-free theorem:

- `not_paraPieceCarvedByMotion_of_straddling`

with supporting private lemmas proving:

- openness of the translated Green sublevel;
- openness of a space-holomorphic motion slice image;
- non-openness of `green`-translate `∩ MandelbrotSet` under the straddling hypothesis.

## Proof architecture

1. The translated Green sublevel
   `{c' | green_function c (c' - c) < (1/2)^n}`
   is open by continuity of the Green function.
2. If `H : SpaceHolomorphicMotion E` and `E` is open, then each slice image
   `H.f t '' E` is open:
   - use local analyticity of the slice from `H.h_space_holo`;
   - apply `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` at a point;
   - rule out the locally constant branch using injectivity of the motion.
3. Under straddling, the target set
   `{c' | green_function c (c' - c) < (1/2)^n} ∩ MandelbrotSet`
   is not open in `ℂ`:
   - the translate itself is connected (`green_sublevel_translate_connected`);
   - if the intersection were open, then both it and its complement inside the translate
     would be open, disjoint, and cover the connected translate;
   - since the translate contains `c ∈ MandelbrotSet`, connectedness forces the whole
     translate into `MandelbrotSet`, contradicting straddling.
4. Therefore a carving witness cannot exist, since it would identify a non-open target
   with an open motion image.

## Verification

Ran successfully:

```bash
lake env lean Mlc/ParaPuzzleCarvingReduction.lean
```

## Constraints check

- No `axiom`, `sorry`, or `admit` added.
- Did not modify `ParaPieceCarvedByMotion`.
- Did not modify the frontier axiom or downstream theorems.
- Did not edit any other Lean source file.
