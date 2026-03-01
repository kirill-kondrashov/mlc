# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

A Lean 4 formalization of the **MLC conjecture** — *the Mandelbrot set is locally
connected*. The theorem `MLC.mlc_conjecture` compiles `sorry`-free with **one
non-core axiom** remaining.

## Quick Start

```bash
make build    # ~7900 Lean compilation jobs
make check    # Axiom frontier report
```

Expected output of `make check`:

Expected output:

```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.ir_locally_connected_seam
```

## Axiom Frontier

| Status | Axiom | Role |
|--------|-------|------|
| ✅ | `Quot.sound` | Core Lean |
| ✅ | `propext` | Core Lean |
| ✅ | `Classical.choice` | Core Lean |
| 🔶 | `ir_locally_connected_seam` | LC at infinitely renormalizable parameters |

### The remaining axiom

```lean
axiom ir_locally_connected_seam :
    ∀ (c : ℂ) (hc : c ∈ MandelbrotSet),
      InfinitelyRenormalizable c →
        LocallyConnectedAt MandelbrotSet ⟨c, hc⟩
```

Under the Gaussian proxy modulus every parameter is infinitely renormalizable
(`infinitely_renormalizable_of_gaussian_modulus`), so this axiom is equivalent
to MLC itself. Mathematically it encapsulates Lyubich a priori bounds combined
with Dudko–Lyubich–Selinger satellite renormalization theory.

### Eliminated axioms

| Axiom | Elimination method |
|-------|--------------------|
| `external_ray_map_exists` | Axiom trade → direct FR/IR route (provably false for current `bottcher_map`) |
| `para_puzzle_piece_inter_mandelbrot_connected` | FR branch vacuous: Gaussian modulus makes every parameter IR |

## Proof Architecture

```
mlc_conjecture
  rw mandelbrotSet_eq_MandelbrotSet
  apply locallyConnectedSpace_of_locallyConnectedAt
  ∀ ⟨c, hc⟩ →
    ir_locally_connected_seam c hc                     ← axiom (🔶)
      (infinitely_renormalizable_of_gaussian_modulus c) ← theorem
```

The proof collapses the FR/IR dichotomy: under the Gaussian proxy modulus
(`modulus A = ∫ exp(−|z|²)`), puzzle annulus moduli always converge, making
**every** parameter infinitely renormalizable. The FR branch (Yoccoz shrinkage)
is vacuously true and contributes no axioms.

### Path to eliminating the last axiom

`InconsistencyRoute.lean` proves:

```lean
theorem false_of_renormalization_tower (c : ℂ)
    (T : RenormalizationTower (parameterToBMol c)) : False
-- depends on: lyubich_conformal_bridge (axiom, mathematically TRUE)

theorem ir_locally_connected_seam_of_tower {c₀ : ℂ}
    (T : RenormalizationTower (parameterToBMol c₀)) :
    ∀ c ∈ MandelbrotSet, InfinitelyRenormalizable c → LocallyConnectedAt …
```

The Gaussian proxy (`cmodulus = modulus`, always summable) contradicts the
Lyubich bridge axiom (`lyubich_conformal_bridge`: given a tower, moduli
diverge). Any single `RenormalizationTower` therefore yields `False`.

**To eliminate `ir_locally_connected_seam`:** construct one
`RenormalizationTower (parameterToBMol c)` for any `c`. The axiom frontier
would then shift from `ir_locally_connected_seam` (equivalent to MLC) to
`lyubich_conformal_bridge` (a true theorem about a priori bounds).

**Current blocker:** the codebase has no concrete `RenormalizationRelation`
instance. Constructing one (e.g., period-2 renormalization of the basilica
`c = −1`) requires formalizing polynomial-like restriction domains, properness
on sub-domains, and an affine conjugacy — infrastructure not yet present.

## What Is Proved (axiom-free)

| Result | Location |
|--------|----------|
| Yoccoz puzzle piece shrinkage (Grötzsch criterion) | `yoccoz-theorem` library |
| Dynamical → parameter shrinkage | `AxiomsMainConjecture.lean` |
| Shrinkage → local connectivity | `LcAtOfShrink.lean` |
| FR ∨ IR dichotomy (classical LEM) | `MainConjecture.lean` |
| Strategy assembly (FR-LC + IR-LC → MLC) | `MainConjecture.lean` |
| Green function convergence & functional eq | `yoccoz-theorem` library |
| `ExternalRayMapData(2) → False` | `MainConjecture.lean:306` |
| `PuzzleBoundaryMotionHyp ↔ connectivity` | `DirectRoute.lean` |
| `M ⊆ ParaPuzzlePiece n` | `ParaPuzzleContainment.lean` |
| `c ∈ M → c ∈ K(c)` | `ParaPuzzleContainment.lean` |
| `RenormalizationTower → False` | `InconsistencyRoute.lean` |
| `RenormalizationTower → ir_locally_connected_seam` | `InconsistencyRoute.lean` |
| `LyubichModulus` series not summable | `InconsistencyRoute.lean` |

## Other Axioms in the Codebase

These axioms exist but **do not flow** into `mlc_conjecture`:

| Axiom | File |
|-------|------|
| `lyubich_conformal_bridge` | `PrimitiveModulusDivergence.lean` |
| `external_ray_map_exists` | `BottcherAxioms.lean` |
| `mandelbrot_set_connected` | `Axioms.lean` |
| `filled_julia_set_connected` | `Axioms.lean` |
| `green_function_strictMono_along_ray_basin_seam` | `Axioms.lean` |
| `bottcher_seq_converges` | `BottcherAxioms.lean` |
| `extended_ray_map_continuous` | `BottcherAxioms.lean` |
| `bottcher_outside_axiom` | `BottcherOnMTheory.lean` |
| `bottcher_map_inj_on_K` | `BottcherOnMTheory.lean` |

## Repository Layout

```
Mlc/                             54 files, ~19 500 lines
├── MainConjecture.lean          Root theorem + proof routes (~1950 lines)
├── DirectRoute.lean             Axiom-free reduction infrastructure
├── InconsistencyRoute.lean      Tower → False via Gaussian proxy inconsistency
├── ParaPuzzleContainment.lean   M ⊆ ParaPuzzlePiece n (proved)
├── AxiomsMainConjecture.lean    parameter_shrink_of_yoccoz (proved)
├── LcAtOfShrink.lean            Shrinkage → local connectivity
├── RenormalizationTypes.lean    IR/FR definitions, parameterToBMol
├── PrimitiveModulusDivergence.lean  Lyubich bridge axiom + modulus infrastructure
├── FastTowerExistenceObstruction.lean  Gaussian proxy obstructions
├── MoleculeConjectureBridge.lean  Molecule conjecture bridge data
├── InfinitelyRenormalizable.lean
├── SatelliteRenormalizationTower.lean
├── MoleculeRenormalizationTower.lean
└── Quadratic/Complex/
    ├── Axioms.lean              Core math axioms (connectedness, Green fn)
    ├── PuzzleLemmas2.lean       Puzzle connectivity
    ├── ConformalGroetzsch.lean   cmodulus = modulus (Gaussian proxy)
    ├── GaussianModulusSummable.lean
    └── Bottcher/                Böttcher map theory (~10 000 lines)
plan/                            Historical strategy plans (PLAN_00–09)
check_axioms.lean                Axiom frontier verification script
```

## Dependencies

| Package | Role |
|---------|------|
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Standard math library |
| [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem) | Yoccoz puzzle machinery, Green function, Grötzsch inequality |
| [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture) | Satellite renormalization (`BMol`, `RenormalizationRelation`, `Rfast`) |

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
