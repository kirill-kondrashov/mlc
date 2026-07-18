# Task 51 — Generalize LC consumer to moving parameter pieces

## What changed

I migrated the local-connectivity consumer in `Mlc/LcAtOfShrink.lean` from the
frozen concrete family `ParaPuzzlePieceAt c n` to a generic depth-indexed family
of parameter pieces.

### New generic interface

Added:

```lean
structure ParameterPieceLcAtData (c : ℂ) (P : ℕ → Set ℂ) : Prop where
  piece_open : ∀ n, IsOpen (P n)
  base_mem : ∀ n, c ∈ P n
  basis : ∀ U ∈ 𝓝 c, ∃ n, P n ⊆ U
  inter_mandelbrot_connected : ∀ n, IsConnected (P n ∩ MandelbrotSet)
```

This keeps the interface honest and minimal:
- openness of each piece,
- basepoint membership,
- neighborhood-basis behavior at the base point,
- connectedness after intersecting with `MandelbrotSet`.

No fake moving family was introduced, and connectedness was not baked into the
piece definition itself.

### New generic lemmas/theorem

Added generic replacements for the para-puzzle-specific consumer plumbing:

- `parameter_piece_induced_connected`
- `parameter_piece_basis_induced`
- `lc_at_of_shrink_of_family_data`

These are the generic analogues of the old subtype-connectedness / induced-basis
/ local-connectivity consumer path, but now parameterized by an arbitrary family
`P`.

### Compatibility preserved

The existing theorem

```lean
lc_at_of_shrink_of_data
```

was preserved as a specialization by instantiating the generic consumer with

```lean
P n := ParaPuzzlePieceAt c n
```

and filling the generic interface from the existing para-puzzle facts:
- `para_puzzle_piece_open`
- `para_puzzle_piece_basis`
- the shrink-to-point hypothesis to derive `base_mem`
- the existing connectedness replacement hook.

So downstream users keep the old API, while the consumer is now reusable with a
future genuine moving-parameter piece family.

## Validation

Targeted check passed:

```bash
lake env lean Mlc/LcAtOfShrink.lean
```

## Scope discipline

Per task instructions, I did **not**:
- define a concrete moving parameter family,
- claim the frontier axiom is discharged,
- remove the existing frozen theorem,
- edit unrelated files.
