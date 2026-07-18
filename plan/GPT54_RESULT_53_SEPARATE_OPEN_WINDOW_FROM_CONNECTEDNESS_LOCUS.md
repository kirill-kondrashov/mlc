# Task 53 — Separate open window from connectedness locus

## Outcome

Corrected the moving-parameter local-connectivity abstraction in
`Mlc/LcAtOfShrink.lean` by separating the ambient open parameter window from the
connectedness locus slice inside it.

This fixes the geometric/API mistake from Result 52: the connectedness locus is
not an ambient open parameter piece, so it should not be fed directly to the
open-neighborhood consumer.

## What changed

### 1. Kept the honest connectedness-locus piece

Retained:

```lean
def connectednessLocusParameterPiece
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) : Set ℂ :=
  (F n).connectednessLocus
```

with its membership/unfolding lemmas.

### 2. Added the ambient open window family

Added:

```lean
def connectednessWindowParameterPiece
    (F : ℕ → BMolParameterFamily ℂ) (n : ℕ) : Set ℂ :=
  (F n).parameterSet
```

with basic membership/unfolding lemmas.

This now distinguishes:
- `W n := connectednessWindowParameterPiece F n` as the ambient open parameter window,
- `K n := connectednessLocusParameterPiece F n` as the connectedness locus inside `W n`.

### 3. Added inclusion lemmas

Added:

```lean
connectednessLocusParameterPiece_subset_window
connectednessLocusParameterPiece_inter_mandelbrot_subset_window_inter_mandelbrot
```

These record the basic geometric relation `K n ⊆ W n` and the induced relative-
Mandelbrot inclusion.

### 4. Replaced the bad adapter by a corrected window/locus adapter

Removed the implicit claim that the locus itself must be open, and introduced:

```lean
structure ConnectednessWindowParameterPieceData
    (c : ℂ) (W K : ℕ → Set ℂ) : Prop where
  window_open : ∀ n, IsOpen (W n)
  base_mem_window : ∀ n, c ∈ W n
  basis : ∀ U ∈ 𝓝 c, ∃ n, W n ⊆ U
  locus_subset_window : ∀ n, K n ⊆ W n
  inter_mandelbrot_connected : ∀ n, IsConnected (W n ∩ MandelbrotSet)
```

plus the projection

```lean
ConnectednessWindowParameterPieceData.toParameterPieceLcAtData
```

This is the smallest honest correction: the generic local-connectivity consumer
still uses the open family `W`, while the separate locus family `K` can be
tracked without being forced to be open.

### 5. Added BMol-family specialization

Added:

```lean
structure ConnectednessLocusWindowFamilyData
    (c : ℂ) (F : ℕ → BMolParameterFamily ℂ) : Prop where ...
```

and the adapter

```lean
ConnectednessLocusWindowFamilyData.toConnectednessWindowParameterPieceData
```

which specializes the general window/locus split to:
- `W n = (F n).parameterSet`
- `K n = (F n).connectednessLocus`

### 6. Added corrected local-connectivity theorem

Added:

```lean
lc_at_of_connectednessWindow_family_data
lc_at_of_connectednessLocus_family_data
```

The first consumes an arbitrary split `(W, K)` with explicit hypotheses; the
second specializes this to an honest `BMolParameterFamily` tower.

## Compatibility

The existing frozen para-puzzle route remains unchanged:

```lean
lc_at_of_shrink_of_data
lc_at_of_shrink_of_connected_at
lc_at_of_shrink
```

still use `ParaPuzzlePieceAt` as before. No frontier axiom changes were made.

## Missing sourced foundation

The repository still does **not** provide a checked concrete theorem saying that
for some analytic quadratic-like family tower:
- the ambient parameter windows are open,
- the windows shrink / form a basis,
- `W n ∩ MandelbrotSet` is connected,
- or the connectedness locus gives the correct relative Mandelbrot slice.

So this task correctly stops at the adapter/interface level and exposes those as
explicit hypotheses.

## Validation

Targeted check passed:

```bash
lake env lean Mlc/LcAtOfShrink.lean
```
