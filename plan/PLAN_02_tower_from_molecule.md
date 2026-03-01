# PLAN 02: Prove `exists_renormalization_tower` from Molecule Structure

**Status:** `RESEARCH — needs feasibility check`
**Difficulty:** Medium-High
**Depends on:** PLAN 01 completed
**Goal:** Eliminate `exists_renormalization_tower` by proving it from `Molecule.molecule_conjecture_refined`

---

## Core Idea

`Molecule.molecule_conjecture_refined` describes the combinatorial structure of
satellite renormalization in the Mandelbrot set. It should imply the existence of
infinitely many nested satellite copies of M, which corresponds to an infinite
renormalization tower.

---

## The Mathematical Argument

The Mandelbrot set contains the main cardioid with period-1 hyperbolic component.
Around it, there are infinitely many satellite components (period-2 bulb, period-4 bulb, ...).
At the boundary of accumulation of the period-2^n bulbs lies the Feigenbaum parameter.

Each satellite component corresponds to a renormalizable parameter:
- Period-2 component → f is renormalizable once (period-2 renormalization)
- Period-4 component → there exist parameters renormalizable twice
- Period-2^n component → parameters renormalizable n times
- Period-2^∞ accumulation point (Feigenbaum) → infinitely renormalizable

**From satellite structure to a tower:**
1. For each n, the period-2^n component gives a `IsFastRenormalizable` map at depth n
2. The limit parameter `c_∞ = lim_{n→∞} c_n` satisfies `∀ n, IsFastRenormalizable (Rfast^n (parameterToBMol c_∞))`
3. This exactly gives `SatelliteRenormalizableTower c_∞`

---

## What's Needed in Lean

### Step 1: Bridge from `MoleculeConjectureRefined` to tower existence

```lean
-- In Mlc/MoleculeToTowerExistence.lean (new file)
theorem exists_tower_of_molecule_conjecture
    (h : MoleculeConjectureRefined) :
    ∃ (c : ℂ), SatelliteRenormalizableTower c
```

This requires:
- Extracting from `h` (which gives a compact invariant set K with Nonempty + IsFastRenormalizable)
  a fixed point `g_∞ : BMol` under `Rfast`
- Showing `Rfast g_∞ = g_∞` and `IsFastRenormalizable (Rfast^n g_∞)` for all n
- Converting `g_∞ = parameterToBMol c_∞` for some `c_∞`

### Step 2: Use fixed-point structure

`MoleculeConjectureRefined` contains `Rfast f_star = f_star` as a condition.
A fixed point `f_star` of `Rfast` with `IsFastRenormalizable f_star` immediately gives:
- `gₙ n = Rfast^n f_star = f_star` (constant sequence)
- `step n := Rfast_spec f_star h_fast : Nonempty (RenormalizationRelation f_star (Rfast f_star))`

But `Rfast f_star = f_star` means all levels are the SAME map, which gives the trivial tower.

**This IS enough** to construct a `RenormalizationTower`!

```lean
-- Concrete tower from a fixed point of Rfast
noncomputable def tower_of_rfast_fixed_point (g : BMol)
    (h_fixed : Rfast g = g) (h_fast : IsFastRenormalizable g) :
    RenormalizationTower g :=
  { gₙ := fun _ => g
    g0 := rfl
    step := fun n => by
      rw [h_fixed]
      exact Rfast_spec g h_fast }
```

### Step 3: Extract the fixed point from `MoleculeConjectureRefined`

`MoleculeConjectureRefined` includes:
- `(_h_ps : ∀ f_star ... Rfast f_star = f_star → ...)` — conditions about fixed points
- `f_ref ∈ K` — a reference map in the invariant set

Need to check if `molecule_conjecture_refined` implies `∃ g, Rfast g = g ∧ IsFastRenormalizable g`.

---

## Investigation Findings (IMPLEMENTED/BLOCKED)

`Molecule/RenormalizationTheorem.lean` has:
```
renormalizable_fixed_point_exists : ∃ f, IsFastRenormalizable f ∧ Rfast f = f
```

BUT this theorem ALSO requires many hypotheses (`h_exists`, `h_norm`, `h_conj`, etc.)
that are themselves deep unproven claims. The Molecule package's "assumptions" are
trivial lemmas that just return their hypotheses — they're not actual proofs.

**Key insight from FeigenbaumFixedPointAssumptions.lean:**
```lean
theorem exists_invariant_polydisk_data_axiom (h_exists : ...) : ... := h_exists
-- This just returns the hypothesis unchanged!
```

**Conclusion:** Cannot prove `exists_renormalization_tower` from current Molecule infrastructure
without adding more axioms (specifically the Siegel disk construction, orbit conditions, etc.).

**The `exists_renormalization_tower` axiom is the minimum standalone axiom needed.**
It captures the Feigenbaum parameter existence as a single clean mathematical statement.

---


- `Molecule/Conjecture.lean` — definition of `molecule_conjecture_refined`
- `Molecule/Rfast.lean` — definition of `Rfast`, `Rfast_spec`
- `Mlc/MoleculeConjectureBridge.lean` — existing bridge infrastructure

---

## Feasibility Assessment

**Positive:**
- `Rfast_spec` already gives `RenormalizationRelation` from `IsFastRenormalizable`
- `MoleculeConjectureRefined` already mentions fixed points of `Rfast`
- The tower construction from a fixed point is trivial (3 lines)

**Negative:**
- We need `∃ g, Rfast g = g ∧ IsFastRenormalizable g` as an extractable fact
- The `MoleculeConjectureRefined` type is very complex; it might give this indirectly
- Might need: `∃ (c : ℂ), parameterToBMol c` corresponds to some BMol in the molecule

---

## Alternative: Weaker Axiom

If the direct proof fails, add a dedicated lemma:
```lean
axiom molecule_has_rfast_fixed_point :
    ∃ (g : BMol), Rfast g = g ∧ IsFastRenormalizable g
```

This is weaker than `exists_renormalization_tower` and more natural (it's the existence
of the Feigenbaum fixed point of the renormalization operator).

---

## Status Markers

- [ ] Read `Molecule/Conjecture.lean` to understand `molecule_conjecture_refined` fully
- [ ] Check if `Rfast_spec` + fixed point gives enough for tower
- [ ] Attempt proof of `exists_tower_of_molecule_conjecture`
- [ ] If stuck, add `molecule_has_rfast_fixed_point` as intermediate axiom
