# PLAN 01: Fix `bottcher_map` at c=2

**Status:** `██░░░░░░░░░░░░░░░░░░` **10%**
**State:** `BLOCKED` — `bottcher_seq_converges` is an axiom; even with correct
definition, proof chain goes through `False.elim` which must be replaced
**Difficulty:** Medium-High
**Risk:** Medium — requires new mathematical formalization, but c=2 is the simplest case.

## Core Idea

The crude `bottcher_map` uses `z/|z|` for the direction, which is wrong.
At c=2, define the **true Böttcher coordinate** using the classical sequence
limit:

```
φ_c(z) = lim_{n→∞} (f_c^n(z))^{1/2^n}
```

Since c=2 is outside the Mandelbrot set, the critical orbit escapes, and
the Böttcher coordinate is defined on all of ℂ\K(2). The limit converges
uniformly on compact subsets of the basin.

## Why This Unsticks Us

With the correct `bottcher_map_two`:
- `bottcher_map_two` IS surjective onto {w : |w| > 1}
  (it's a biholomorphism from ℂ\K(2) to ℂ\D̄)
- `ExternalRayMapData (2)` (adapted to `bottcher_map_two`) becomes provable
- The approach-to-1 sequence argument no longer leads to False because
  the true Böttcher map maps K(2) to the unit circle with all directions
  covered (not just `z/|z|`)
- The vacuous proof chain is replaced by a real mathematical argument

## Implementation Steps

### Step 1: Define the true Böttcher coordinate at c=2

```lean
noncomputable def true_bottcher_map_two (z : ℂ) : ℂ :=
  limUnder atTop (fun n => ((quadratic_map (2 : ℂ))^[n] z) ^ ((1 : ℂ) / 2 ^ n))
```

### Step 2: Prove convergence on the basin

For c=2, ALL points except K(2) escape. Need to show:
- The sequence `(f_2^n(z))^{1/2^n}` converges for z ∉ K(2)
- Convergence is locally uniform on compact subsets of ℂ\K(2)

This uses the standard estimate: `|f_c^n(z)|^{1/2^n} → exp(G(c,z))` for the
modulus (already formalized via `green_function`), and the argument converges
because the corrections are summable (geometric series in 1/2^n).

### Step 3: Prove key properties

- `|true_bottcher_map_two z| = exp(G(2, z))` for z ∉ K(2)
- `true_bottcher_map_two` is holomorphic on ℂ\K(2)
- `true_bottcher_map_two` conjugates f_2 to squaring: φ(f_2(z)) = φ(z)²
- `true_bottcher_map_two` maps ℂ\K(2) biholomorphically onto ℂ\D̄

### Step 4: Construct ExternalRayMapData

Define the inverse ray map as the inverse of `true_bottcher_map_two`.
Right inverse: φ(φ⁻¹(w)) = w for |w| > 1.
Left inverse: φ⁻¹(φ(z)) = z for z far from K(2).

### Step 5: Rewire mlc_conjecture

**Key:** We need to either:
(a) Redefine `bottcher_map` globally to equal `true_bottcher_map_two` at c=2, or
(b) Show that the main proof only needs properties that both maps share
    (modulus = exp(G)), plus surjectivity for the true map.

Option (b) is cleaner: the proof chain only uses `BottcherSurjOnExterior`,
which says `∀ w, 1 < ‖w‖ → ∃ z, bottcher_map c z = w`. If we can show
surjectivity for the TRUE map and then connect it to the existing
`BottcherSurjOnExterior` definition, we're done.

But `BottcherSurjOnExterior` is stated in terms of the crude `bottcher_map`,
so surjectivity of the true map doesn't directly give us surjectivity of the
crude map. We'd need to:
- Redefine `bottcher_map` to use the true coordinate, OR
- Bypass `BottcherSurjOnExterior` and connect the true map directly to MLC.

### Step 6: Handle the contradiction lemma

`false_of_bottcher_approach_to_one_seq_preimage_data_two` would need to be
REMOVED or weakened, since with the correct Böttcher map, the approach-to-1
data is no longer contradictory. The proof chain would need to go through
`MainPathData` via a real proof, not via `False.elim`.

This is the hardest part: we'd also need to fill in the actual MLC strategy
components (`PuzzleBoundaryMotionHyp`, IR classification, molecule bridge).

## Alternative: Minimal Change Variant

Instead of fixing everything, exploit the fact that the proof only needs
`BottcherSurjOnExterior (2)`. Define `true_bottcher_map_two`, prove its
surjectivity, then show:

```lean
lemma bottcherSurjOnExterior_two_of_true_bottcher :
    BottcherSurjOnExterior (2 : ℂ) := by
  -- PROBLEM: BottcherSurjOnExterior is stated in terms of crude bottcher_map,
  -- not true_bottcher_map_two. These are different functions.
```

This doesn't directly work because `BottcherSurjOnExterior` references the
crude map. So we'd need to refactor.

## Feasibility Note (2026-03-01)

`bottcher_root_seq` is already defined in `BottcherOutsidePlan.lean:249`:
```lean
def bottcher_root_seq (c : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((fun w => w ^ 2 + c)^[n] z) ^ ((2 : ℂ) ^ n)⁻¹
```

However, its convergence proof (`bottcher_root_seq_tendsto`, line 261)
delegates to the axiom `bottcher_seq_converges` (BottcherAxioms.lean:297).
That axiom claims convergence to the CRUDE `bottcher_map`, which is
mathematically wrong. The true limit is the correct Böttcher coordinate.

**Even if we fix the definition and prove convergence**, the existing
proof chain from `BottcherSurjOnExterior(2)` goes through `False.elim`.
Making the map correct would make `ExternalRayMapData(2)` TRUE but would
BREAK the existing proof (the contradiction lemma would no longer hold).
We'd then need Plan 02's components to complete the proof.

## Dependencies

- Mathlib: complex powers, holomorphic function theory
- Yoccoz library: Green function properties, escape bounds

## Risk Assessment

- **Risk of scope creep:** High — defining the true Böttcher coordinate properly
  and proving biholomorphicity is significant formalization work.
- **Risk of cascading changes:** Medium — changing `bottcher_map` globally would
  affect many files, but we could scope it to c=2.
- **Mitigation:** Start with Step 1-2 (definition + convergence) and assess
  feasibility before committing to the full plan.
