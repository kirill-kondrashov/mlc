# Situation Analysis (Current State)

**Read this first before working on any plan.**

---

## Current Axiom Frontier of `mlc_conjecture`

```
Quot.sound, propext, Classical.choice      ← Lean core (non-negotiable)
molecule_renormalizable_fixed_point_data   ← Inou-Shishikura/Feigenbaum hypotheses
fixedPoint_parameter_model_data            ← Straightening Theorem (Douady-Hubbard)
lyubich_conformal_bridge                   ← Lyubich's a priori bounds
```

`check_axioms.lean` verifies exactly this set. Build passes ✓.

---

## How We Got Here

1. **`ir_locally_connected_seam` was circular**: under the Gaussian proxy modulus,
   every c is InfinitelyRenormalizable, so the axiom was equivalent to MLC itself.

2. **InconsistencyRoute** (`Mlc/InconsistencyRoute.lean`) was already built:
   - `LyubichModulus = 1` (constant) → never summable
   - `lyubich_conformal_bridge`: divergence of LyubichModulus → divergence of cmodulus
   - Gaussian proxy: `cmodulus` is always summable
   - Any `RenormalizationTower (parameterToBMol c)` → `False`

3. **Replaced `ir_locally_connected_seam`** with `exists_parameter_model_rfast_fixed_point`,
   which gives the tower needed for the InconsistencyRoute.

---

## The Routes Forward

See PLAN_01 through PLAN_05 for detailed strategies.

| Plan | Action | Difficulty | Status |
|------|--------|-----------|--------|
| PLAN_01 | Split monolithic axiom into two cleaner ones | Easy | ✅ DONE |
| PLAN_02 | Prove `molecule_renormalizable_fixed_point_data` | Very Hard | ❌ Blocked (trivial slice) |
| PLAN_03 | Prove `fixedPoint_parameter_model_data` (Straightening) | Very Hard | ❌ Blocked (degenerate parameterToBMol) |
| PLAN_04 | Eliminate `lyubich_conformal_bridge` | Very Hard | Long-term |
| PLAN_05 | BMol-generalization: bypass Straightening Theorem | Medium | **⭐ READY** |

**Recommended next step: PLAN_05.** It reduces from 3 to 2 non-core axioms in ~2 hours.
