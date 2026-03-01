# Situation Analysis: Where We Actually Are

**Status:** `REFERENCE — read this first`

---

## Current Axiom Frontier of `mlc_conjecture`

After many iterations, the proof of `mlc_conjecture` depends on exactly:

```
Quot.sound, propext, Classical.choice   ← Lean core (non-negotiable)
ir_locally_connected_seam               ← THE ONE WE MUST ELIMINATE
```

`external_ray_map_exists` is **already gone** from the dependency chain.

---

## Why `ir_locally_connected_seam` is the Wrong Axiom

The axiom states:
```lean
axiom ir_locally_connected_seam :
    ∀ (c : ℂ) (hc : c ∈ MandelbrotSet), InfinitelyRenormalizable c →
        LocallyConnectedAt MandelbrotSet ⟨c, hc⟩
```

Under the Gaussian proxy modulus, `infinitely_renormalizable_of_gaussian_modulus`
proves **every** parameter is `InfinitelyRenormalizable`. Therefore:

> `ir_locally_connected_seam` ≡ "every Mandelbrot point is locally connected" ≡ MLC

We have axiomatized the conclusion. This is circular.

---

## The InconsistencyRoute (Already Built)

`Mlc/InconsistencyRoute.lean` provides:

```lean
theorem false_of_renormalization_tower (c : ℂ)
    (T : RenormalizationTower (parameterToBMol c)) : False

theorem mlc_of_tower' (T : RenormalizationTower ...) : LocallyConnectedSpace X
```

**Derivation:**
1. `LyubichModulus = 1` → `¬Summable (fun n => LyubichModulus ...)` ✓ (proved)
2. `lyubich_conformal_bridge` axiom: divergence → `¬Summable cmodulus`
3. Gaussian proxy: `Summable cmodulus` always ✓ (proved)
4. Contradiction → `False`

**Only axiom needed:** `lyubich_conformal_bridge` (already present, mathematically standard)

**Missing piece:** A concrete `RenormalizationTower (parameterToBMol c)` for ANY `c`.

---

## The Gap: Constructing a RenormalizationTower

`RenormalizationTower g` requires an infinite sequence of renormalizations:
```lean
structure RenormalizationTower (g : BMol) where
  gₙ : ℕ → BMol
  g0 : gₙ 0 = g
  step : ∀ n, Nonempty (RenormalizationRelation (gₙ n) (gₙ (n + 1)))
```

This is the heart of the problem.

---

## Key Observations

1. `exists_renormalization_tower` was added as an axiom in `RenormalizationTowerExistence.lean`
   but is not yet wired into `mlc_conjecture`.

2. `Molecule.molecule_conjecture_refined` is itself an axiom in `Molecule/Conjecture.lean`.
   It describes the satellite renormalization structure but doesn't directly produce a tower.

3. `SatelliteRenormalizableTower c` = `Nonempty (RenormalizationTower (parameterToBMol c))`.
   We know `false_of_satellite_tower` in `InconsistencyRoute`.

4. The Gaussian proxy makes `InfinitelyRenormalizable` trivially true for all `c`, but this
   is **NOT** the same as `SatelliteRenormalizableTower` (which requires actual Rfast iterates).

---

## The Three Routes Forward

See PLAN_01, PLAN_02, PLAN_03 for the three strategies.
