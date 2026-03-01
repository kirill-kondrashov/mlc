# PLAN 03: Construct the Basilica Tower Concretely

**Status:** `HARD — requires new mathematical formalization`
**Difficulty:** High
**Depends on:** Nothing (can proceed independently)
**Goal:** Construct `RenormalizationTower (parameterToBMol (-1))` by explicit definition

---

## Core Idea

The basilica map `f(z) = z² - 1` is period-doubling renormalizable:
- `f²(z) = z⁴ - 2z²` has 0 as a superattracting period-2 fixed point
- The renormalized map (after rescaling) is again a quadratic-like map
- Iterating this gives an infinite tower (period-2, period-4, period-8, ...)

Unlike PLAN 02 (which extracts a tower from abstract molecule structure), this
plan builds the tower CONCRETELY for c = -1.

---

## Mathematical Setup

For `f = f_{-1}: z ↦ z² - 1`:

### Level 1: First renormalization
- Let `V₁ = B(0, r₁)` (disk around 0)
- Let `U₁ = f_{-1}⁻¹(V₁) ∩ B(0, r₁')` (preimage component)
- `f_{-1}² : U₁ → V₁` is a degree-2 holomorphic proper map
- After rescaling by `ψ₁(z) = α₁·z`, we get `g₁ = ψ₁⁻¹ ∘ f_{-1}² ∘ ψ₁`
- `g₁` is in the same form as f_{c₁} for some c₁ close to -1

### Level 2: Second renormalization
- Apply the same procedure to `g₁`
- Get `g₂ = ψ₂⁻¹ ∘ g₁² ∘ ψ₂`

### Infinite tower
- `RenormalizationTower.gₙ n = gₙ`
- `step n : RenormalizationRelation gₙ gₙ₊₁`

---

## What's Needed in Lean

### Step 1: Define explicit domains
```lean
-- Explicit disks for the basilica renormalization
noncomputable def basilicaV (n : ℕ) : Set ℂ := Metric.ball 0 (2⁻¹^n)
noncomputable def basilicaU (n : ℕ) : Set ℂ := ...
```

### Step 2: Prove the renormalization relation
```lean
theorem basilica_renormalization_relation (n : ℕ) :
    Nonempty (RenormalizationRelation (basilicaMap n) (basilicaMap (n + 1)))
```

### Step 3: Build the tower
```lean
noncomputable def basilicaTower : RenormalizationTower (parameterToBMol (-1)) :=
  { gₙ := basilicaMap
    g0 := by rfl
    step := fun n => ⟨basilicaRelation n⟩ }
```

---

## Key Challenge: `RenormalizationRelation`

What does `RenormalizationRelation` require? From `Mlc/MoleculeRenormalizationTower.lean`:
```lean
structure RenormalizationTower (g : BMol) where
  step : ∀ n : ℕ, Nonempty (RenormalizationRelation (gₙ n) (gₙ (n + 1)))
```

Need to find `RenormalizationRelation` definition. It's likely in the `Molecule` library
and requires:
- Proper inclusion of domains: `V ⊆ U`
- `g.f : U → V` is a branched cover of degree `p ≥ 2`
- Some normalization condition

---

## Why This Is Hard

1. Need to verify the scaling constants `α_n → 0` explicitly
2. Need to show `g_n.f` are ALL proper maps of degree 2 to their target
3. Need the Straightening Theorem to show `g_n` is actually a `parameterToBMol`-type map
4. The `BMol` structure imposes specific conditions (U, V, normalization)

---

## Alternative: Toy Model

Instead of the actual basilica, construct a "trivial" tower:

A `RenormalizationRelation f g` with `f = g = const_map` where const_map
is some degenerate but valid BMol. This shows `RenormalizationTower exists` 
without any complex analysis.

Check if `RenormalizationRelation` allows degenerate maps.
If it does, this becomes trivial.

---

## Feasibility

**Positive:**
- The mathematics is completely rigorous and classical
- No new axioms needed — just formalization work
- Can be done with `sorry` at intermediate steps, then filled in later

**Negative:**
- Requires substantial work on `RenormalizationRelation` formalization
- Period-doubling geometry is non-trivial to formalize exactly
- Depends on how restrictive `BMol` structure is

---

## Recommended First Action

Check `RenormalizationRelation` definition and see what conditions it imposes.
Then check if a constant/degenerate map satisfies them.
