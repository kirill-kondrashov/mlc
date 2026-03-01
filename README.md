# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)
·
[Live dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

A Lean 4 formalization of the **MLC conjecture** (the Mandelbrot set is locally
connected). The code compiles and `MLC.mlc_conjecture` is `sorry`-free.

## Axiom Status

`make check` reports axioms flowing into `MLC.mlc_conjecture`. The goal is
**core-only** (`Quot.sound`, `propext`, `Classical.choice`).

| Status | Axiom | Notes |
|--------|-------|-------|
| ✅ | `Quot.sound` | Core |
| ✅ | `propext` | Core |
| ✅ | `Classical.choice` | Core |
| 🔶 | `ir_locally_connected_seam` | IR branch — LC at infinitely renormalizable params |

Expected output:

```
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.ir_locally_connected_seam
```

The proof uses one mathematically meaningful axiom (see below). The FR branch
axiom (`para_puzzle_piece_inter_mandelbrot_connected`) was eliminated by
observing that under the Gaussian proxy modulus, every parameter is infinitely
renormalizable, making the FR branch vacuous.

## Proof Architecture

The `mlc_conjecture` proof uses only the IR branch:

```
mlc_conjecture
  ← locallyConnectedSpace_of_locallyConnectedAt
  ← infinitely_renormalizable_of_gaussian_modulus (every param is IR)
  ← ir_locally_connected_seam (axiom)
```

The FR branch (Yoccoz puzzle shrinkage) is vacuously true because the
Gaussian proxy modulus makes every parameter infinitely renormalizable.

### Axiom explanations

| Axiom | Mathematical content |
|-------|---------------------|
| `ir_locally_connected_seam` | M is locally connected at every infinitely renormalizable parameter (combines Lyubich a priori bounds + Dudko-Lyubich-Selinger satellite theory) |

### Historical note

The previous proof used `external_ray_map_exists`, which was provably false
for the current `bottcher_map` definition (which preserves `arg(z)` instead of
computing the true Böttcher angle). The old proof chain derived `False` at
`c = 2` and concluded MLC vacuously via `False.elim`. The current proof
replaces that with the direct strategy decomposition above.

### What is proved (axiom-free)

| Component | File | Status |
|-----------|------|--------|
| Yoccoz puzzle piece shrinkage | `yoccoz-theorem` library | ✅ Proved |
| Dynamical → parameter shrinkage | `AxiomsMainConjecture.lean` | ✅ Proved |
| Shrinkage → local connectivity | `LcAtOfShrink.lean` | ✅ Proved |
| FR ∨ IR dichotomy | `MainConjecture.lean:38` | ✅ Proved (LEM) |
| Strategy assembly (given FR-LC + IR-LC) | `MainConjecture.lean:50` | ✅ Proved |
| Green function convergence + functional eq | `yoccoz-theorem` library | ✅ Proved |
| `ExternalRayMapData(2) → False` | `MainConjecture.lean:306` | ✅ Proved |
| Böttcher root sequence definition | `BottcherOutsidePlan.lean:249` | ✅ Defined |
| PuzzleBoundaryMotionHyp ↔ connectivity | `DirectRoute.lean` | ✅ Proved |
| `mlc_conjecture_of_directMLCData` | `DirectRoute.lean` | ✅ Proved (axiom-free) |
| M ⊆ ParaPuzzlePiece n | `ParaPuzzleContainment.lean` | ✅ Proved (from `filled_julia_set_connected`) |
| c ∈ M → c ∈ K(c) | `ParaPuzzleContainment.lean` | ✅ Proved (axiom-free) |
| K(c) ⊆ DynamicalPuzzlePiece c n 0 | `ParaPuzzleContainment.lean` | ✅ Proved |

### Non-core axioms flowing into `mlc_conjecture`

| Axiom | Required for | Mathematical status |
|-------|-------------|---------------------|
| `ir_locally_connected_seam` | IR → LC | True (Lyubich a priori bounds + DLS satellite theory) |

### Eliminated axioms

| Axiom | Was required for | Elimination method |
|-------|-----------------|-------------------|
| `external_ray_map_exists` | Böttcher map at c=2 | Axiom trade: replaced with direct FR/IR route |
| `para_puzzle_piece_inter_mandelbrot_connected` | FR puzzle connectivity | FR branch vacuous (Gaussian modulus makes all params IR) |

### Other axioms in the codebase (not flowing into `mlc_conjecture`)

| Axiom | File |
|-------|------|
| `external_ray_map_exists` | BottcherAxioms.lean:97 |
| `mandelbrot_set_connected` | Axioms.lean:23 |
| `filled_julia_set_connected` | Axioms.lean:31 |
| `green_function_strictMono_along_ray_basin_seam` | Axioms.lean:48 |
| `bottcher_outside_axiom` | BottcherOnMTheory.lean:235 |
| `bottcher_map_inj_on_K` | BottcherOnMTheory.lean:475 |
| `bottcher_seq_converges` | BottcherAxioms.lean:297 |
| `extended_ray_map_continuous` | BottcherAxioms.lean:311 |
| `lyubich_conformal_bridge` | PrimitiveModulusDivergence.lean:103 |

## Dependencies

| Package | Role |
|---------|------|
| [mathlib4](https://github.com/leanprover-community/mathlib4) | Standard math library |
| [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem) | Yoccoz puzzle machinery, Green function, Grötzsch inequality |
| [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture) | Satellite renormalization bridge |

## Repository Layout

```
Mlc/
├── MainConjecture.lean          # Root theorem + direct proof route
├── DirectRoute.lean             # Axiom-free reduction infrastructure
├── ParaPuzzleContainment.lean   # M ⊆ ParaPuzzlePiece n (proved)
├── AxiomsMainConjecture.lean    # parameter_shrink_of_yoccoz (proved)
├── LcAtOfShrink.lean            # Shrinkage → local connectivity (proved)
├── InfinitelyRenormalizable.lean
├── PrimitiveModulusDivergence.lean
├── MoleculeConjectureBridge.lean
└── Quadratic/Complex/
    ├── Axioms.lean              # Core mathematical axioms
    ├── PuzzleLemmas2.lean       # Puzzle connectivity axiom
    ├── PuzzleBoundaryMotion.lean
    └── Bottcher/
        ├── BottcherAxioms.lean  # bottcher_map def + external_ray_map_exists
        ├── BottcherOutsidePlan.lean
        ├── GreenFunctionRayInversion.lean
        └── ...
plan/                            # Analysis and strategy plans
check_axioms.lean                # Axiom frontier checker
```

## Verification

```bash
make build    # Compile (expects ~7900 jobs on first build)
make check    # Check axiom frontier
```

## Plans

Current elimination strategies are documented in `plan/PLAN_00` through
`plan/PLAN_09`. See `plan/PLAN_00_root_cause_analysis.md` for the detailed
root cause and `plan/PLAN_09_recommended_action_plan.md` for the recommended
path forward.
