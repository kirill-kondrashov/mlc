# Root Cause Analysis: Why We're Stuck

**Status:** `REFERENCE` — read this before working on any plan.

## The Critical Discovery

The entire MLC proof is **vacuously true via `False.elim`**.

### Proof chain

```
mlc_conjecture
  → mlc_conjecture_of_external_ray_map_exists_two
      externalRayMapData_two_root_frontier
  → mlc_conjecture_of_externalRayMapData_two
  → mlc_conjecture_of_bottcherSurjOnExterior_two_via_fiber
  → mlc_conjecture_of_bottcherApproachOneSeqFiberData_two
  → mlc_conjecture_of_bottcherApproachToOneSeqPreimageData_two
  → mlc_conjecture_of_mainPathData
      (mainPathData_of_bottcherApproachToOneSeqPreimageData_two h_data)
```

And `mainPathData_of_bottcherApproachToOneSeqPreimageData_two` (line 548) is:

```lean
have hFalse : False := false_of_bottcher_approach_to_one_seq_preimage_data_two h_data
exact False.elim hFalse
```

### Why `BottcherApproachToOneSeqPreimageData (2)` is False

The lemma `false_of_bottcher_approach_to_one_seq_preimage_data_two` (line 306)
proves: if a sequence `z_n` has `bottcher_map 2 (z_n) → 1`, then:
1. The `z_n` are bounded (Green function values → 0, escape bound controls norm).
2. Extract convergent subsequence `z_{φ(n)} → a`.
3. By continuity of Green function: `G(2, a) = 0`, so `a ∈ K(2)`.
4. By continuity of `bottcher_map`: `bottcher_map 2 a = 1`.
5. But `bottcher_map_eq_one_not_mem_K_two` says: if `z ∈ K(2)` and
   `bottcher_map 2 z = 1`, then `z/|z| = 1` (z is real positive), but
   **all real numbers escape for c=2** (`ofReal_mem_basin_two`), so
   no real number is in K(2). Contradiction.

### Why `ExternalRayMapData (2)` is provably False

The current `bottcher_map` is defined as:
```lean
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  let u := if z = 0 then 1 else z / ↑‖z‖
  u * ↑(Real.exp (MLC.Quadratic.green_function c z))
```

This is **NOT** the Böttcher coordinate. It preserves the geometric argument
`arg(z)` while the true Böttcher coordinate rotates it. This means:

- `|bottcher_map c z| = exp(G(c, z))` ✓ (correct modulus)
- `arg(bottcher_map c z) = arg(z)` ✗ (wrong angle — should be the Böttcher angle)

For c=2 (outside the Mandelbrot set), all real numbers escape, so there are
no real-valued points in K(2). The crude `bottcher_map` maps K(2)\{0} to the
unit circle via `z ↦ z/|z|`. No K(2) point maps to the real direction `1`.
Therefore, no Böttcher preimage sequence can converge to 1, so surjectivity
near the real-axis part of the unit circle fails.

Since `ExternalRayMapData (2)` implies `BottcherSurjOnExterior (2)` implies
`BottcherApproachToOneSeqPreimageData (2)` implies `False`, we have:

> **`ExternalRayMapData (2)` is provably False in the current formalization.**

### Why every constructive path has failed

**All v1–v30 plans tried to constructively prove something that is provably
false.** Specifically:

- `DirectProperLocalWitnessTwo` (proper + local homeomorphism of restricted
  map) would imply surjectivity (covering map of connected space), which
  implies `BottcherSurjOnExterior (2)`, which implies `False`.
- `QuadraticMapIterLeftInverseOnBasin` is proved false for all c.
- All Green-function inversion paths produce `ExternalRayMapData (2)`, which
  is false.
- All injectivity + surjectivity composite paths lead to the same dead end.

**The dead end is not in the proof strategy — it's in the `bottcher_map`
definition.**

## What must change

To eliminate the axiom without adding new axioms or hypotheses to
`mlc_conjecture`, we need ONE of:

1. **Fix `bottcher_map`** to be the correct Böttcher coordinate (angle-correct),
   making `ExternalRayMapData` constructively provable.
2. **Bypass the Böttcher map entirely** — prove `LocallyConnectedSpace
   mandelbrotSet` through the strategy decomposition
   (`mlc_strategy_of_branchLocalData`) or another mathematical route.
3. **Replace the vacuous proof chain** with a non-vacuous one that doesn't
   go through `BottcherApproachToOneSeqPreimageData → False → MainPathData`.
