# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository formalizes a Lean 4 proof of Mandelbrot local connectivity
modulo two explicitly named project-level axioms.

## Mathematical target

For $c,z\in\mathbb C$, let

$$
f_c(z)=z^2+c,\qquad
\mathcal M=\{c:(f_c^n(0))_{n\geq0}\text{ is bounded}\},\qquad
K_c=\{z:(f_c^n(z))_{n\geq0}\text{ is bounded}\}.
$$

Let $G_c$ be the dynamical Green function and define

$$
A_n(c)=\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\},\qquad
T_n(c)=A_n(c)\cap\mathcal M.
$$

The formal target is

```lean
MLC.mlc_conjecture : LocallyConnectedSpace MLC.mandelbrotSet
```

For $c\in\mathcal M$, the frozen parameter puzzle satisfies

```lean
ParaPuzzlePieceAt c n = {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
```

and the checked development proves

$$
\mathrm{ParaPuzzlePieceAt}(c,n)=A_n(c).
$$

## Checked Lean state

`MLC.mlc_conjecture` contains no `sorry`.

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

The first three axioms are Lean foundations. The project frontier is:

1. **Straddling parameter connectivity**

   ```lean
   MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
   ```

   Mathematically, for $c\in\mathcal M$,

   $$
   A_n(c)\not\subseteq\mathcal M
   \Longrightarrow
   T_n(c)\text{ is connected}.
   $$

   The case $A_n(c)\subseteq\mathcal M$ is a separate theorem-level
   containment result. The remaining case is the Douady--Hubbard/Yoccoz
   parameter--dynamical correspondence for a straddling piece.

2. **Virtual near-Molecule renormalization**

   ```lean
   MLC.residualOpenVirtualNearMoleculeAxiom
   ```

   This is the conjunction of the root-facing forms of Dudko--Lyubich
   Problems 4.3 and 4.4: pseudo-Siegel a priori bounds in the remaining
   unbounded satellite cases and the Virtual Molecule near-degenerate
   classification.

## Proved core

- $K_c$ is connected for $c\in\mathcal M$.
- $S_n(c)=\{z:G_c(z)<2^{-n}\}$ is connected for $c\in\mathcal M$, by
  harmonicity of $G_c$ on the basin of infinity and the harmonic minimum
  principle.
- $A_n(c)$ is connected by translation.
- `ParaPuzzlePieceAt c n = A_n(c)` for $c\in\mathcal M$.
- The subset containment stratum for $T_n(c)$ is proved.
- Given connected parameter pieces whose intersection shrinks to $c$,
  `Mlc/LocalConnectivity.lean` derives local connectivity at $c$.
- `Mlc/MotivicFiniteIncidence.lean` proves that a connected finite attachment
  graph has no nontrivial idempotent in its incidence endomorphism ring.

The root assembly splits into finitely renormalizable and infinitely
renormalizable parameters. The finite branch uses Yoccoz shrinking; the
infinite branch uses the virtual near-Molecule axiom.

## Motivic/K-theoretic route

The repository records the categorical contract needed to discharge the
straddling frontier, but does not formalize Efimov's relative localizing
motives. For an independently defined realization locus $Q_n(P)$, the
required comparison is

$$
Q_n(P(c,n))=T_n(c),
$$

and a separation must induce a nontrivial idempotent in the endomorphisms of
an indecomposable motive. This contract is
[`GreenSublevelStraddlingMotivicFrontier`](Mlc/MotivicConnectednessFrontier.lean).
The finite incidence shadow and the topological obstruction are in
[`Mlc/MotivicFiniteIncidence.lean`](Mlc/MotivicFiniteIncidence.lean) and
[`Mlc/MotivicIntersectionNoGo.lean`](Mlc/MotivicIntersectionNoGo.lean).

The missing mathematical inputs are an independently defined finite
Pacman/parapuzzle realization, its connectedness theorem, and the exact
comparison with $T_n(c)$. BGT and Efimov provide the intended categorical
framework; they do not supply these geometric statements.

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
| Root theorem and residual renormalization input | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Parameter-connectivity frontier | [`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean) |
| Local-connectivity consumer | [`Mlc/LocalConnectivity.lean`](Mlc/LocalConnectivity.lean) |
| Motivic frontier contract | [`Mlc/MotivicConnectednessFrontier.lean`](Mlc/MotivicConnectednessFrontier.lean) |
| Finite incidence shadow | [`Mlc/MotivicFiniteIncidence.lean`](Mlc/MotivicFiniteIncidence.lean) |
| Axiom report | [`check_axioms.lean`](check_axioms.lean) |

## Sources

- [Dudko, arXiv:2512.24171](https://arxiv.org/abs/2512.24171)
- [Pacman/motive bridge](https://github.com/kirill-kondrashov/raw/blob/main/bridge_between_pacman_renormalization_and_noncommutative_motives.md)
- [BGT, arXiv:1001.2282](https://arxiv.org/abs/1001.2282)
- [Efimov, arXiv:2510.17010](https://arxiv.org/abs/2510.17010)

Dependencies: [Lean 4](https://github.com/leanprover/lean4),
[mathlib4](https://github.com/leanprover-community/mathlib4),
[yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem), and
[molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture).

Lean toolchain: `leanprover/lean4:v4.28.0`.
