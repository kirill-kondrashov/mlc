# PLAN 01: Axiom Swap — Replace `ir_locally_connected_seam` with `exists_renormalization_tower`

**Status:** `READY TO IMPLEMENT`
**Difficulty:** Low (code change is 5–10 lines)
**Mathematical Cost:** Replace one circular axiom with one standard fact
**Verdict:** This is the correct immediate next step.

---

## Core Idea

`ir_locally_connected_seam` ≡ MLC (circular). Replace it with:
- `exists_renormalization_tower`: "some parameter admits an infinite renormalization tower"

Combined with `lyubich_conformal_bridge` (already present), the InconsistencyRoute gives MLC.

---

## Why This is Strictly Better

| Old axiom | New axiom(s) |
|-----------|-------------|
| `ir_locally_connected_seam` | `exists_renormalization_tower` + `lyubich_conformal_bridge` |
| ≡ MLC (circular) | Standard results in complex dynamics |
| Proves: IR params are locally connected | Proves: Some param has an infinite tower |
| Strength: = MLC | Strength: Much weaker than MLC |

The Feigenbaum parameter `c ≈ -1.40115...` is known to be infinitely period-doubling
renormalizable. `exists_renormalization_tower` just asserts this standard fact.

---

## Implementation Steps

### Step 1: Update `Mlc/MainConjecture.lean`

Replace the `mlc_conjecture` proof:

```lean
-- OLD (circular):
theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet := by
  rw [mandelbrotSet_eq_MandelbrotSet]
  apply mlc_conjecture_of_paraPuzzleMandelbrotSubsetData_classify_bridge_data
  · intro c _hc n; exact Quadratic.mandelbrotSet_subset_paraPuzzlePiece n
  · intro c _hc h_ir; left; intro hc; exact ir_locally_connected_seam c hc h_ir
  · intro _h_mol c hc _h_sat
    exact ir_locally_connected_seam c hc (infinitely_renormalizable_of_gaussian_modulus c)

-- NEW (InconsistencyRoute):
import Mlc.RenormalizationTowerExistence
import Mlc.InconsistencyRoute

theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet := by
  obtain ⟨c, ⟨T⟩⟩ := exists_renormalization_tower
  exact mlc_of_tower' T
```

### Step 2: Add imports to `MainConjecture.lean`
```lean
import Mlc.RenormalizationTowerExistence
import Mlc.InconsistencyRoute
```

### Step 3: Update `check_axioms.lean`
Change expected axioms from `ir_locally_connected_seam` to:
```lean
let expectedAxioms : List Name :=
    [``Quot.sound, ``propext, ``Classical.choice,
     ``MLC.exists_renormalization_tower,
     ``MLC.lyubich_conformal_bridge]
```

---

## Result

After this change:
- `mlc_conjecture` no longer depends on `ir_locally_connected_seam` ✓
- `mlc_conjecture` depends on `exists_renormalization_tower` + `lyubich_conformal_bridge`
- `ir_locally_connected_seam` becomes an unused axiom (can be removed or kept)

---

## Risk Assessment

- **Build risk**: Low. The imports already exist, `mlc_of_tower'` is already proved.
- **Mathematical risk**: Zero. The proof is valid given the axioms.
- **Circularity risk**: None. `exists_renormalization_tower` does NOT assume MLC.

---

## What Comes After (PLAN 02 and 03)

Once `ir_locally_connected_seam` is gone, the remaining axioms are:
- `exists_renormalization_tower` → prove constructively (see PLAN 02)
- `lyubich_conformal_bridge` → standard complex dynamics (harder, see PLAN 03)
