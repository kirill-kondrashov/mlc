# Task 52 — Define connectedness-locus parameter piece

## Outcome

Landed an honest moving-parameter piece definition in `Mlc/LcAtOfShrink.lean`
based directly on the existing quadratic-like connectedness-locus foundation in
`Mlc/BMolFilledJulia.lean`.

## What was added

### 1. Connectedness-locus-backed parameter piece

Added:

```lean
def connectednessLocusParameterPiece
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) : Set ℂ :=
  (F n).connectednessLocus
```

This is an honest moving-family piece: level `n` is defined from the connectedness
locus of the supplied `BMolParameterFamily` at that level.

It is **not** defined from:
- a frozen Green translate,
- an exact image of a preexisting frozen piece,
- an `IsConnected` witness.

### 2. Unfolding / membership lemmas

Added:

```lean
@[simp] lemma mem_connectednessLocusParameterPiece_iff ...
@[simp] lemma connectednessLocusParameterPiece_eq ...
```

So membership unfolds to:

```lean
c ∈ connectednessLocusParameterPiece F n ↔
  c ∈ (F n).parameterSet ∧ FilledJuliaConnected ((F n).map c)
```

### 3. Explicit adapter to the generic LC consumer

Added a focused hypothesis package:

```lean
structure ConnectednessLocusParameterPieceData
    (c : ℂ) (F : ℕ → BMolParameterFamily ℂ) : Prop where
  piece_open : ∀ n, IsOpen (connectednessLocusParameterPiece F n)
  base_mem : ∀ n, c ∈ connectednessLocusParameterPiece F n
  basis : ∀ U ∈ 𝓝 c, ∃ n, connectednessLocusParameterPiece F n ⊆ U
  inter_mandelbrot_connected :
    ∀ n, IsConnected (connectednessLocusParameterPiece F n ∩ MandelbrotSet)
```

plus the adapter

```lean
ConnectednessLocusParameterPieceData.toParameterPieceLcAtData
```

and a convenience theorem

```lean
lc_at_of_connectednessLocus_family_data
```

which feeds the new honest piece family into the generic Task 51 consumer.

## Audit result / foundation status

The repository already contains the minimal honest family-level foundation:
- `Molecule.BMolParameterFamily`
- `Molecule.BMolParameterFamily.connectednessLocus`
- `Molecule.filledJuliaSet`
- `Molecule.FilledJuliaConnected`

I also audited `Mlc/AnalyticQuadraticLikeFamilyCore.lean`: it is intentionally an
incomplete analytic core and does **not** yet provide a checked concrete theorem
that some connectedness locus is open, connected, shrinking, or forms the needed
basis. So I did **not** fabricate a concrete family instance from that file.

## Smallest honest next task

The next task is to construct or import a concrete depth-indexed family
`F : ℕ → BMolParameterFamily ℂ` together with checked proofs of the four fields of
`ConnectednessLocusParameterPieceData`:
- openness of each connectedness locus,
- basepoint membership,
- neighborhood-basis/shrinking behavior,
- connectedness of `connectednessLocusParameterPiece F n ∩ MandelbrotSet`.

That is the exact missing family-level foundation still required before this route
can replace the frozen para-puzzle specialization in actual MLC proofs.

## Validation

Targeted check passed:

```bash
lake env lean Mlc/LcAtOfShrink.lean
```
