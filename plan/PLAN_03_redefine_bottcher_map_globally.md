# PLAN 03: Redefine `bottcher_map` Globally

**Status:** `█░░░░░░░░░░░░░░░░░░░` **5%**
**State:** `BLOCKED` — same blockers as Plan 01 with larger scope
**Difficulty:** High
**Risk:** Medium — focused refactor with clear mathematical target.

## Core Idea

The crude `bottcher_map` defined as `(z/|z|) · exp(G(c,z))` has the correct
modulus but the wrong angle. Replace it globally with the standard Böttcher
coordinate defined via the sequence limit:

```
φ_c(z) = lim_{n→∞} (f_c^n(z))^{1/2^n}
```

Once the definition is correct:
- `ExternalRayMapData c` becomes provable for c ∈ M (Riemann mapping theorem)
- `ExternalRayMapData (2)` becomes provable for c = 2 (biholomorphism of basin)
- The approach-to-1 contradiction disappears (true Böttcher map IS surjective)
- `mlc_conjecture` can use a non-vacuous proof chain

## Why the Current Definition Is Wrong

The crude map `(z/|z|) · exp(G(c,z))` preserves the geometric direction of z:
```
arg(bottcher_map(c, z)) = arg(z)
```

The true Böttcher coordinate satisfies:
```
arg(φ_c(z)) = arg(z) + Σ_{k=0}^∞ (1/2^{k+1}) · correction_k(c, z)
```

The corrections encode how `f_c` rotates points near infinity. Near infinity,
the corrections vanish (so the crude map is asymptotically correct), but near
K(c), the corrections accumulate and make the angle completely different.

## Implementation Steps

### Step 1: Define the Böttcher sequence

```lean
noncomputable def bottcher_seq (c : ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  ((quadratic_map c)^[n] z) ^ ((1 : ℂ) / 2 ^ n)
```

Note: the complex power `w ^ (1/2^n)` requires choosing a branch. Use the
principal branch (or the branch that's continuous on the basin of infinity).

### Step 2: Prove convergence on the basin

For z in the basin of infinity:
- `|bottcher_seq c z n| = |f_c^n(z)|^{1/2^n} → exp(G(c,z))` (modulus convergence)
- The argument converges because `|arg(f_c^n(z)) / 2^n - arg(f_c^{n+1}(z)) / 2^{n+1}|`
  is summable (dominated by const/|f_c^n(z)|)

This is a standard complex analysis result but requires careful branch
management in Lean/Mathlib.

### Step 3: Define the corrected `bottcher_map`

```lean
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  if z ∈ basin_of_infinity c then
    limUnder atTop (bottcher_seq c z)
  else
    z / ↑‖z‖  -- or any convention for K(c) points
```

### Step 4: Prove the functional equation

```lean
theorem bottcher_map_conjugates (c z : ℂ) (hz : z ∈ basin_of_infinity c) :
    bottcher_map c (quadratic_map c z) = (bottcher_map c z) ^ 2
```

### Step 5: Prove surjectivity

For c ∈ M: the Böttcher coordinate maps the basin bijectively onto {|w| > 1}.
This follows from the Riemann mapping theorem + normalization at infinity.

For c ∉ M (like c=2): the Böttcher coordinate maps ℂ\K(c) bijectively onto
ℂ\D̄ (where D̄ is the closed unit disk).

### Step 6: Construct `ExternalRayMapData`

The right inverse is φ_c⁻¹ (inverse of Böttcher map).
The left inverse for large |z| follows from bijectivity on the basin.

### Step 7: Verify compatibility

After redefining `bottcher_map`, check that:
- `norm_bottcher_eq_exp_green` still holds (it should, since |φ_c(z)| = exp(G))
- Other lemmas about `bottcher_map` remain valid or can be adjusted
- `false_of_bottcher_approach_to_one_seq_preimage_data_two` NO LONGER holds
  (which is correct — remove it and the False.elim chain)

### Step 8: Build a real proof chain

With the correct map, `BottcherSurjOnExterior (2)` is TRUE. But the
existing proof from there goes through `False.elim` (via the contradiction).
We need to either:
- Build `MainPathData` from surjectivity through a real proof, or
- Find a different route from surjectivity to MLC that doesn't go through
  the contradiction lemma.

**THIS IS THE KEY CHALLENGE:** Even with the correct Böttcher map, the
current proof ARCHITECTURE goes through `False.elim`. Fixing the map removes
the axiom but breaks the proof chain (because the contradiction no longer
works). We'd need Plan 02's components to complete the proof.

## Assessment

This plan fixes the root cause (wrong definition) but exposes that the
proof chain is vacuous and needs real mathematical content. It should be
combined with Plan 02 or a plan that replaces the `False.elim` chain.

## Interaction with Other Plans

- **Combines with Plan 02:** After fixing the map, use the strategy
  decomposition to provide the actual proof.
- **Alternative to Plan 01:** Plan 01 fixes only at c=2; this plan fixes
  globally.
- **Prerequisite for Plan 05:** If we want the Böttcher map to be correct,
  do this first.
