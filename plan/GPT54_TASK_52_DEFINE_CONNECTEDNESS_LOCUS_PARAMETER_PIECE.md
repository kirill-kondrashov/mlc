# TASK 52 — Define a connectedness-locus-backed moving parameter piece

## Global context

The live frontier remains:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The recommended route is to remove the frozen parameter object from the
dependency graph:

```text
moving quadratic-like family
→ connectedness locus
→ genuine finite parameter piece
→ relative connectedness and shrink-compatible consumer
→ delete frozen straddling axiom
```

Result 51 already landed the generic consumer interface
`ParameterPieceLcAtData` in `Mlc/LcAtOfShrink.lean`.

The repository already has the honest low-level definitions:

```lean
Molecule.BMolParameterFamily
Molecule.BMolParameterFamily.connectednessLocus
Molecule.filledJuliaSet
Molecule.FilledJuliaConnected
```

It does not yet have a verified concrete proper/unfolded/equipped parameter
family theorem producing the full classical connectedness-locus topology.

## Deliverable

Create a focused module defining a moving parameter piece from supplied
quadratic-like family data. The definition should be equivalent to:

```lean
def connectednessLocusParameterPiece
    (F : Molecule.BMolParameterFamily ℂ) : Set ℂ :=
  F.connectednessLocus
```

or a depth-indexed analogue if that is more useful for later integration.

Provide:

- clean membership/unfolding lemmas;
- restriction/domain lemmas showing the piece lies in the family parameter
  domain;
- an explicit adapter theorem/structure listing the additional hypotheses
  needed to instantiate `ParameterPieceLcAtData`:
  openness, basepoint membership, neighborhood-basis behavior, and relative
  connectedness inside `MandelbrotSet`.

The adapter must not prove those hypotheses by circularity. It should make clear
which facts are supplied by a future sourced proper unfolded equipped family.

## Constraints

- Do not define the piece using the frozen Green translate.
- Do not use exact-image packaging or an `IsConnected` witness as the piece
  definition.
- Do not claim Theorem 10.1/Corollary 10.3/10.15 has been formalized unless
  checked Lean declarations actually provide it.
- Do not pretend `AnalyticQuadraticLikeFamilyCore` is already proper, unfolded,
  or equipped.
- No `sorry`, `admit`, or new axiom.
- Do not alter the frontier axiom or current frozen compatibility route.
- Do not commit.

## Verification

Run the focused module check and then:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_52_DEFINE_CONNECTEDNESS_LOCUS_PARAMETER_PIECE.md`

Report:

- the exact new definition and module;
- the membership/unfolding API;
- the adapter to `ParameterPieceLcAtData`;
- the first missing deep theorem needed for an actual axiom-removing instance.
