# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository contains a compact Lean 4 formalization of the Mandelbrot
local-connectivity conjecture, conditional on two explicit mathematical inputs.

## Target

For $c,z\in\mathbb C$, write $f_c(z)=z^2+c$ and let $\mathcal M$ be the
Mandelbrot set. The checked root theorem is

```lean
MLC.mlc_conjecture : LocallyConnectedSpace MLC.mandelbrotSet
```

The parameter pieces used by the proof are

$$
A_n(c)=\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\},\qquad
T_n(c)=A_n(c)\cap\mathcal M.
$$

## Checked Lean state

`MLC.mlc_conjecture` is `sorry`-free. Its only project-level axioms are:

1. `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`:
   connectedness of $T_n(c)$ in the genuine straddling case
   $A_n(c)\not\subseteq\mathcal M$.
2. `MLC.residualOpenVirtualNearMoleculeAxiom`: the root-facing conjunction of
   Dudko--Lyubich Problems 4.3 and 4.4 (pseudo-Siegel bounds and the virtual
   near-Molecule classification).

The remaining reported axioms are Lean foundations:

```text
Quot.sound
propext
Classical.choice
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.residualOpenVirtualNearMoleculeAxiom
- MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

## Proved core

- $K_c$ is connected for $c\in\mathcal M$.
- The dynamical Green sublevels $\{z:G_c(z)<2^{-n}\}$ are connected.
- Translation identifies the frozen parameter pieces with those sublevels.
- The subset stratum of $T_n(c)$ is connected without an axiom.
- Yoccoz shrinking and the Molecule bridge assemble local connectivity.
- Retained glue forwards to standard Mathlib/Yoccoz APIs, including
  `locallyConnectedSpace_iff_connected_subsets`, `Set.image_iInter`,
  `integral_biUnion_finset`, `modulus`, and `groetzsch_criterion`.

`check_axioms.lean` imports only `Mlc.Core`, and every tracked `Mlc/**/*.lean`
module is in that transitive closure. `Mlc.lean` is retained as the package
entry point and `check_axioms.lean` as the executable checker; no stale project
Lean modules remain. Every retained declaration is in the root dependency
closure, with `MLC.mlc_conjecture` as the intentional terminal node. The
complete tracked Lean source pass is warning-free.

## Validation

```bash
make build
make check
./scripts/verify_output.sh
```

## Core files

| Purpose | Path |
| --- | --- |
| Public root | [`Mlc.lean`](Mlc.lean) |
| Root theorem | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Parameter frontier | [`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean) |
| Green-sublevel proof | [`Mlc/GreenSublevelConnectedDirect.lean`](Mlc/GreenSublevelConnectedDirect.lean) |
| Molecule bridge | [`Mlc/MoleculeToParameterShrink.lean`](Mlc/MoleculeToParameterShrink.lean) |
| Axiom checker | [`check_axioms.lean`](check_axioms.lean) |

## Sources and dependencies

- [Dudko, arXiv:2512.24171](https://arxiv.org/abs/2512.24171)
- [Efimov, arXiv:2510.17010](https://arxiv.org/abs/2510.17010)
- [Lean 4](https://github.com/leanprover/lean4)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.28.0`.
