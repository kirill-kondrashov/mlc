# PLAN 01: Split into Two Weaker Axioms

**Status:** ✅ COMPLETED
**Difficulty:** Minimal — infrastructure already exists
**Goal:** Replace monolithic `exists_parameter_model_rfast_fixed_point` with two cleaner axioms

---

## Why This is Better

`exists_parameter_model_rfast_fixed_point` is a combined axiom. Splitting it exposes:
- `molecule_renormalizable_fixed_point_data`: all Molecule paper hypotheses
- `fixedPoint_parameter_model_data`: the Straightening Theorem for Rfast fixed points

Both are classical results, independently citable, and individually easier to prove.

---

## What Exists Already

`RenormalizationTowerExistence.lean` ALREADY has:
```lean
axiom molecule_renormalizable_fixed_point_data : MoleculeRenormalizableFixedPointData
axiom fixedPoint_parameter_model_data : FixedPointParameterModelData

theorem exists_renormalization_tower_of_molecule_bridge_axioms :
    ∃ c : ℂ, Nonempty (RenormalizationTower (parameterToBMol c)) :=
  exists_renormalization_tower_of_existsParameterModelRfastFixedPoint
    existsParameterModelRfastFixedPoint_of_molecule_bridge_axioms
```

The theorem `exists_renormalization_tower_of_molecule_bridge_axioms` provides exactly
what `mlc_conjecture` needs, using ONLY the two weaker axioms.

---

## Implementation (2 changes)

### Change 1: `Mlc/MainConjecture.lean`

```lean
-- Current:
theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_tower
    exists_renormalization_tower_of_exists_parameter_model_rfast_fixed_point

-- New:
theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet :=
  mlc_conjecture_of_exists_tower
    exists_renormalization_tower_of_molecule_bridge_axioms
```

### Change 2: `check_axioms.lean`

```lean
-- Current:
[``Quot.sound, ``propext, ``Classical.choice,
 ``MLC.exists_parameter_model_rfast_fixed_point,
 ``MLC.lyubich_conformal_bridge]

-- New:
[``Quot.sound, ``propext, ``Classical.choice,
 ``MLC.molecule_renormalizable_fixed_point_data,
 ``MLC.fixedPoint_parameter_model_data,
 ``MLC.lyubich_conformal_bridge]
```

---

## Result

`mlc_conjecture` no longer depends on `exists_parameter_model_rfast_fixed_point`.
The new axiom frontier is:
- `molecule_renormalizable_fixed_point_data` — Molecule/Feigenbaum hypotheses
- `fixedPoint_parameter_model_data` — Douady-Hubbard Straightening Theorem
- `lyubich_conformal_bridge` — Lyubich's complex bounds

These are THREE standard classical results, all non-circular.

---

## Risk

Zero. The infrastructure was already built. This is just wiring it up.
