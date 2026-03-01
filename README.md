# MLC — Mandelbrot Local Connectivity in Lean 4

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
| ❌ | `MLC.Quadratic.external_ray_map_exists` | Last non-core axiom — see below |

`make check` currently **fails** because of the remaining non-core axiom.

## Root Cause: Why the Axiom Cannot Be Eliminated by Local Changes

The current `bottcher_map` definition (BottcherAxioms.lean:17–19) is:

```lean
noncomputable def bottcher_map (c : ℂ) (z : ℂ) : ℂ :=
  let u := if z = 0 then 1 else z / ↑‖z‖
  u * ↑(Real.exp (MLC.Quadratic.green_function c z))
```

This is **not the true Böttcher coordinate** `φ_c(z) = lim (f_c^n(z))^{1/2^n}`.
It preserves `arg(z)` instead of computing the Böttcher angle, giving the wrong
angular structure. As a consequence:

1. `ExternalRayMapData(2)` (a consequence of the axiom at `c = 2`) is
   **provably false** — no point in K(2) maps to direction 1 under the crude
   map, because all reals escape at `c = 2`.
2. The proof of `mlc_conjecture` is therefore **vacuous**: it derives
   `BottcherApproachToOneSeqPreimageData(2)` from the axiom, then proves
   `False` from it (MainConjecture.lean:306), and concludes MLC via
   `False.elim` (MainConjecture.lean:551).
3. Eliminating the axiom collapses the `False.elim` chain and requires
   replacing it with a genuine proof.

## Proof Architecture

The formalization has a complete proof *skeleton* that reduces MLC to two
independent hypotheses:

```
mlc_conjecture
  ← mlc_conjecture_of_mainPathData
  ← mlc_conjecture_of_motionHyp_track12_data
  ← mlc_strategy_of_branchLocalData         ← dichotomy (FR ∨ IR)

FR branch: PuzzleBoundaryMotionHyp → Yoccoz shrinkage → local connectivity
IR branch: classification (Primitive ∨ Satellite) + molecule conjecture → LC
```

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

### What is NOT proved (blocks axiom elimination)

| Gap | Required for | Status |
|-----|--------------|--------|
| Puzzle piece ∩ M connected | FR → LC | Axiom (`para_puzzle_piece_inter_mandelbrot_connected`) |
| Holomorphic motion of puzzle boundaries | FR → LC (alternative) | Unproved (`PuzzleBoundaryMotionHyp`) |
| IR classification oracle | IR → LC | Unproved (`IRClassificationData`) |
| Molecule conjecture | IR satellite → LC | Unproved (`MoleculeConjectureRefined`) |
| Lyubich conformal bridge | IR primitive → LC | Axiom (`lyubich_conformal_bridge`) |
| Böttcher sequence convergence | Correct Böttcher coord | Axiom (`bottcher_seq_converges`) |

**Closing any single column (FR or IR) is insufficient — both are needed.**

## Other Axioms in the Codebase

These exist but do **not** flow into `mlc_conjecture`:

| Axiom | File |
|-------|------|
| `mandelbrot_set_connected` | Axioms.lean:23 |
| `filled_julia_set_connected` | Axioms.lean:31 |
| `green_function_strictMono_along_ray_basin_seam` | Axioms.lean:48 |
| `para_puzzle_piece_inter_mandelbrot_connected` | PuzzleLemmas2.lean:66 |
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
├── MainConjecture.lean          # Root theorem + proof chain
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
        ├── BottcherAxioms.lean  # bottcher_map def + external_ray_map_exists axiom
        ├── BottcherOutsidePlan.lean  # bottcher_root_seq (correct sequence)
        ├── GreenFunctionRayInversion.lean
        └── ...
plan/                            # Elimination strategy plans (PLAN_00–09)
check_axioms.lean                # Axiom frontier checker
```

## Verification

```bash
make build    # Compile (expects ~7900 jobs on first build)
make check    # Check axiom frontier (currently FAILS — see above)
```

## Plans

Current elimination strategies are documented in `plan/PLAN_00` through
`plan/PLAN_09`. See `plan/PLAN_00_root_cause_analysis.md` for the detailed
root cause and `plan/PLAN_09_recommended_action_plan.md` for the recommended
path forward.
