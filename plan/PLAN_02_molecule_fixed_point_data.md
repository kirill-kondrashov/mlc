# PLAN 02: Prove `molecule_renormalizable_fixed_point_data`

**Status:** BLOCKED — trivial slice definitions make core hypotheses unprovable
**Difficulty:** Very Hard
**Depends on:** PLAN_01 completed

---

## What It Is

```lean
axiom molecule_renormalizable_fixed_point_data : MoleculeRenormalizableFixedPointData
```

`MoleculeRenormalizableFixedPointData` packs the 6 hypotheses of
`Molecule.renormalizable_fixed_point_exists`. These correspond to the Inou-Shishikura
machinery for renormalization operator fixed points.

---

## Key Finding: Trivial Slice Definitions Block Everything

`Molecule/BanachSlice.lean` defines:
```lean
def slice_chart (_f_star : BMol) : BMol → SliceSpace := fun _ => 0
def slice_domain (_ : BMol) : Set BMol := univ
def slice_operator (_f_star : BMol) : SliceSpace → SliceSpace := fun _ => 0
```

All three are constant placeholders. This has major consequences for the 6 hypotheses:

---

## The 6 Hypotheses — Feasibility

### h_conj ✅ PROVABLE
`slice_operator f_ref (slice_chart f_ref x) = slice_chart f_ref (Rfast x)` reduces to `0 = 0`.
This is trivially true by the constant definitions. **Can be proved today.**

### h_exists ❌ UNPROVABLE (root blocker)
Requires: compact convex `P`, and `K = {f | slice_chart f_ref f ∈ P}` with `K.Finite ∧ K.Nonempty`.
- Any `P` containing `0` gives `K = Set.univ` — not finite (BMol is infinite type)
- Any `P` not containing `0` gives `K = ∅` — not nonempty
**No choice of P works with the trivial slice_chart = constant 0.**

### h_norm ❌ UNPROVABLE
`∀ K : Set BMol, (∀ f ∈ K, IsFastRenormalizable f) ∧ ...`
With `K = univ` (forced by trivial slice), this says ALL BMol maps are fast-renorm — false.

### h_ps ❌ Unknown
Requires Siegel disk geometry for Rfast fixed points. No path from current code.

### h_orbit ❌ Unknown
Orbit covering conditions. Requires full Inou-Shishikura theory.

### h_unique ❌ Unknown
Uniqueness of Rfast fixed point. Requires contraction argument not present.

---

## Feasibility Assessment

**BLOCKED.** Root cause: `slice_chart = fun _ => 0` makes `h_exists` unsatisfiable.
Until the Molecule package implements a real (non-constant) `slice_chart`, this cannot be proved.

A real `slice_chart f_ref g` would map `g` to its Taylor coefficient in a Banach space
of polynomial-like maps (the "slice" in Inou-Shishikura theory). This is a major project.

---

## Path to Unblocking

Implement in the Molecule package:
1. Real `slice_chart f_ref : BMol → SliceSpace` (e.g., coefficient of leading term)
2. Real `slice_operator f_ref : SliceSpace → SliceSpace` (linearized Rfast)
3. Then prove invariant polydisk exists (Banach fixed-point or Schauder theorem)

This is long-term research. For now: keep `molecule_renormalizable_fixed_point_data` as axiom.
See PLAN_05 for reducing the overall axiom count without solving this problem.

