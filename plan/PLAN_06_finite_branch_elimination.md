# PLAN 06: Eliminate `finite_branch_local_connectivity`

**Status:** READY TO IMPLEMENT  
**Difficulty:** Medium  
**Goal:** Remove `finite_branch_local_connectivity` from the root frontier
without introducing any new axioms.

---

## Why This Is the Right Next Step

The current non-core frontier is:

- `finite_branch_local_connectivity`
- `problem43_pseudoSiegelAPrioriBounds`
- `problem44_virtualMolecule`
- `problem45_virtualNearMoleculeRenormalization`

The paper `arXiv:2512.24171` only justifies the remaining **IR/satellite**
seams (Problems 4.3 / 4.4 / 4.5). The finite branch should therefore be
internalized, not left as a permanent peer axiom.

If this plan succeeds, the root theorem frontier drops to exactly:

- `problem43_pseudoSiegelAPrioriBounds`
- `problem44_virtualMolecule`
- `problem45_virtualNearMoleculeRenormalization`

plus the Lean core axioms.

---

## Key Observation

The finite branch has two logical ingredients:

1. connectedness of `ParaPuzzlePieceAt c n ∩ MandelbrotSet`
2. shrinkage of `⋂ n ParaPuzzlePieceAt c n` to `{c}`

Only the second ingredient is still truly axiomatic.

### Connectedness route is already available

The repo already has:

- `mandelbrot_subset_paraPuzzlePiece`
- `ParaPuzzleMandelbrotSubsetData`
- `para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data`
- `finite_lc_provider_of_paraPuzzleConnectedData`

So the connectedness side should be proved without adding any new FR axiom.

### Shrinkage is the real blocker

The current axiom chain is:

```lean
para_iInter_eq_singleton_of_dyn_iInter_eq_singleton
→ parameter_shrink_of_yoccoz
→ finite_branch_local_connectivity
```

So the correct target is to **theoremize this chain**, not replace it with a
different root-facing FR assumption.

---

## Concrete Implementation Plan

### Step 1: Prove
`Quadratic.PrincipalNest.para_iInter_eq_singleton_of_dyn_iInter_eq_singleton`

File:
- `Mlc/Quadratic/Complex/PrincipalNestShrink.lean`

Current state:
- this theorem is still an axiom

Why it matters:
- it is the exact bridge from Yoccoz’s dynamical shrink statement
  `⋂ n DynamicalPuzzlePiece c n 0 = {0}`
  to parameter shrink
  `⋂ n ParaPuzzlePieceAt c n = {c}`

### Step 2: Theoremize `parameter_shrink_of_yoccoz`

File:
- `Mlc/AxiomsMainConjecture.lean`

Current state:
- still an axiom

Plan:
- use `MLC.yoccoz_theorem`
- feed the dynamical singleton conclusion into the theoremized
  `para_iInter_eq_singleton_of_dyn_iInter_eq_singleton`

### Step 3: Rewire finite branch through theoremized data

Files:
- `Mlc/MainConjecture.lean`
- possibly `Mlc/LcAtOfShrink.lean`

Plan:
- route the FR branch through:
  - `mandelbrot_subset_paraPuzzlePiece`
  - connectedness on `ParaPuzzlePieceAt c n ∩ MandelbrotSet`
  - theoremized `parameter_shrink_of_yoccoz`
- remove `finite_branch_local_connectivity` from the root theorem

### Step 4: Update the frontier

Files:
- `check_axioms.lean`
- `README.md`
- `site/`

Expected result:
- the root theorem should only depend on Problems 4.3 / 4.4 / 4.5

---

## Why This Introduces No New Axioms

This plan does **not** replace one FR axiom by another. Instead it:

- proves the connectedness side from existing subset lemmas
- proves the shrink side from the already intended Yoccoz route
- removes `finite_branch_local_connectivity` outright

So the axiom count goes down, and the only remaining non-core frontier is the
paper-facing IR/satellite one.

---

## Relation to `2512.24171`

The paper’s new content addresses the IR/satellite side:

- Problem 4.3: pseudo-Siegel a priori bounds
- Problem 4.4: virtual Molecule near-degenerate regime
- Problem 4.5: virtual near-Molecule renormalization

This plan complements that update by removing the leftover **finite branch**
axiom, which is not one of the paper’s remaining open seams.

---

## Success Criterion

After this plan:

1. `finite_branch_local_connectivity` disappears from `check_axioms.lean`
2. `make build` passes
3. `make check` passes
4. `bash scripts/verify_output.sh` passes
5. `README.md` states that the only remaining non-core axioms are
   Problems 4.3 / 4.4 / 4.5
