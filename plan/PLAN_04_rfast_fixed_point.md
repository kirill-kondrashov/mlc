# PLAN 04: Exploit the Rfast Fixed-Point Directly

**Status:** `PROMISING — needs 2-hour investigation`
**Difficulty:** Medium
**Depends on:** Understanding `Molecule/Rfast.lean` and `Rfast_spec`
**Goal:** Construct a tower using `Rfast_spec` on any fixed point

---

## Core Observation

`SatelliteRenormalizationTower.lean` already has:
```lean
noncomputable def renormalizationTower_of_infinitelyFast (g : BMol)
    (h : IsInfinitelyFastRenormalizable g) :
    RenormalizationTower g
```

where `IsInfinitelyFastRenormalizable g = ∀ n, IsFastRenormalizable ((Rfast^[n]) g)`.

So we **only need** to find ONE `g : BMol` with `∀ n, IsFastRenormalizable (Rfast^n g)`.

---

## If `g` is a Fixed Point of `Rfast`

If `Rfast g = g`, then `Rfast^n g = g` for all `n`, so:

```
∀ n, IsFastRenormalizable (Rfast^n g) ↔ ∀ n, IsFastRenormalizable g ↔ IsFastRenormalizable g
```

And then `renormalizationTower_of_infinitelyFast g (fun _ => h)` gives the tower.

**Finding a fixed point:**
Does `Molecule.molecule_conjecture_refined` give us `∃ g, Rfast g = g ∧ IsFastRenormalizable g`?

Looking at `MoleculeConjectureRefined`, one of its hypotheses includes:
```lean
(_h_ps : ∀ f_star (D : Set ℂ), ... → Rfast f_star = f_star → ...)
```

And:
```lean
(_h_orbit : ∀ (f_star : BMol) ... Rfast f_star = f_star → IsFastRenormalizable f_star → ...)
```

These hypotheses ARE passed a `f_star` with `Rfast f_star = f_star`. The question is:
does the conjunction of all hypotheses imply the existence of such an `f_star`?

**Answer: YES** — `molecule_conjecture_refined` is `∀ h_exists h_conj h_norm h_ps h_orbit ..., Q`.
It requires many hypotheses to conclude `Q` (local connectivity). But as an axiom,
`Molecule.molecule_conjecture_refined` IS proved (as a Lean axiom). So calling it
with all the required hypotheses would prove `Q`.

**But we need** `∃ g, Rfast g = g ∧ IsFastRenormalizable g` — a DIFFERENT conclusion.

---

## Alternative: Check if `Rfast_spec` can be applied to `parameterToBMol 0`

What is `parameterToBMol 0`? This is `f_0 : z ↦ z²`, the simplest map.
- Is `z²` fast renormalizable? Almost certainly YES (it's the simplest map in M).
- `Rfast (parameterToBMol 0)` is the next renormalization.
- Is `IsFastRenormalizable` preserved by `Rfast`?

If `IsFastRenormalizable` is closed under iteration (i.e., if `g` is FR then `Rfast g` is FR too),
then from `IsFastRenormalizable (parameterToBMol 0)` we'd get the full tower.

---

## Key Question to Answer

1. What does `IsFastRenormalizable` mean exactly? (Check `Molecule/IsFastRenormalizable.lean`)
2. Is there a lemma `rfast_preserves_fast_renormalizable : IsFastRenormalizable g → IsFastRenormalizable (Rfast g)`?
3. Is `parameterToBMol 0` fast renormalizable?

---

## Concrete Plan

### Step 1: Investigate
```bash
grep -rn "IsFastRenormalizable\|Rfast_spec" Molecule/ --include="*.lean" | head -30
```

### Step 2: Try the fixed-point tower
```lean
-- If we can prove:
lemma zero_map_fast_renormalizable : IsFastRenormalizable (parameterToBMol 0) := by ...

-- And Rfast preserves fast-renormalizability:
lemma rfast_preserves (g : BMol) (h : IsFastRenormalizable g) :
    IsFastRenormalizable (Rfast g) := by ...

-- Then:
noncomputable def someTower : ∃ c, Nonempty (RenormalizationTower (parameterToBMol c)) :=
  ⟨0, ⟨renormalizationTower_of_infinitelyFast _ (fun n => rfast_iter_preserves n _ zero_fast)⟩⟩
```

---

## Investigation Results

**BLOCKED.** The Molecule package has `renormalizable_fixed_point_exists` which proves
`∃ f, IsFastRenormalizable f ∧ Rfast f = f`, BUT this theorem takes many hypotheses
that are themselves unproved (e.g., `h_norm : ∀ K, ∀ f ∈ K, IsFastRenormalizable f ∧ ...`
which is a UNIVERSAL claim about all sets K — unprovable without axioms).

There is NO concrete `g : BMol` anywhere in the Molecule package that's proved fast
renormalizable without hypotheses.

## Current Status

`exists_renormalization_tower` remains as the minimal standalone axiom. It IS provable
in principle (the Feigenbaum parameter exists) but requires formalizing:
1. The Siegel disk construction
2. The Molecule invariant set data
3. The orbit conditions
These are all as hard as the Molecule Conjecture itself.

---


- `renormalizationTower_of_infinitelyFast` is ALREADY proved in `SatelliteRenormalizationTower.lean`
- We just need the infinite-fast-renormalizability property
- This is a natural mathematical fact about the simplest map `z²`
- It avoids constructing explicit domains, scaling maps, etc.

---

## Expected Axioms After This Plan

If successful (by proving `IsFastRenormalizable` closure under `Rfast`):
- Depends only on `Rfast_spec` (in `Molecule/Rfast.lean`)
- Depends on `Molecule.molecule_conjecture_refined` (if needed for closure)
- NO new axioms for the tower itself — just formalization of existing Molecule theory
