# Situation Analysis (Current State)

**Read this first before working on any plan.**

---

## Current Axiom Frontier of `mlc_conjecture`

```text
Quot.sound, propext, Classical.choice
finite_branch_local_connectivity
problem43_pseudoSiegelAPrioriBounds
problem44_virtualMolecule
problem45_virtualNearMoleculeRenormalization
```

`check_axioms.lean` verifies exactly this set.

---

## What the Current Frontier Means

- `problem43_pseudoSiegelAPrioriBounds`
  = Problem 4.3 in `arXiv:2512.24171`
- `problem44_virtualMolecule`
  = Problem 4.4 / virtual Molecule near-degenerate regime
- `problem45_virtualNearMoleculeRenormalization`
  = §4.5 / primitive-first ql virtual near-Molecule case
- `finite_branch_local_connectivity`
  = the remaining finite-renormalizable branch payload

The paper-facing open strategy is therefore already isolated on the
IR/satellite side. The next cleanup step is to remove the **finite branch** axiom
without adding any new ones.

---

## Main Planning Conclusion

The current `plan/PLAN_01` through `plan/PLAN_05` files describe **older axiom
frontiers**. They are still useful as historical notes, but they are no longer
the current recommended execution order.

The active next problem is:

> eliminate `finite_branch_local_connectivity` constructively, while leaving the
> remaining root frontier at exactly Problems 4.3 / 4.4 / 4.5.

---

## Key Technical Finding

The finite branch splits into two parts:

1. **Connectedness of** `ParaPuzzlePieceAt c n ∩ M`
2. **Shrinkage of** `⋂ n ParaPuzzlePieceAt c n` to `{c}`

Only the second part is the serious blocker.

### Connectedness is already close to theoremized

Because `ParaPuzzlePieceAt c n` is currently simplified and the repo already has
`MandelbrotSet ⊆ ParaPuzzlePieceAt c n`, the connectedness part can be routed
through:

- `mandelbrot_subset_paraPuzzlePiece`
- `para_puzzle_piece_inter_mandelbrot_connected_data_of_mandelbrot_subset_data`
- `finite_lc_provider_of_paraPuzzleConnectedData`

This means the finite branch should **not** be attacked by adding a new
boundary-motion or connectedness axiom.

### Shrinkage is the real blocker

The actual obstacle is the theorem chain:

- `para_iInter_eq_singleton_of_dyn_iInter_eq_singleton`
- `parameter_shrink_of_yoccoz`
- `finite_lc_provider_of_motionHyp`

Both root-facing simplifications still rest on the parameter shrink step, and
that step is still axiomatic.

---

## Recommended Next Plan

Follow `PLAN_06_finite_branch_elimination.md`.

That plan is the current recommended next implementation pass.

---

## Status of the Older Plans

| Plan | Role now |
|------|----------|
| `PLAN_01_split_axioms.md` | Historical |
| `PLAN_02_molecule_fixed_point_data.md` | Historical / upstream architecture |
| `PLAN_03_straightening_theorem.md` | Historical / upstream architecture |
| `PLAN_04_lyubich_bridge.md` | Historical / long-term cleanup |
| `PLAN_05_bMol_generalization.md` | Historical / older root route |

They may still contain reusable local ideas, but they do **not** describe the
current 4.3 / 4.4 / 4.5 root frontier.
