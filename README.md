# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository formalizes parts of the Mandelbrot local-connectivity
conjecture in Lean 4. The root theorem is `sorry`-free and currently depends
on two explicitly named project-level axioms.

## Contents

- [Mathematical setting](#mathematical-setting)
- [Formal theorem](#formal-theorem)
- [Axiom frontier](#axiom-frontier)
- [Proved components](#proved-components)
- [Current discharge target](#current-discharge-target)
- [Pacman and motive bridge](#pacman-and-motive-bridge)
- [Efimov and BGT source layer](#efimov-and-bgt-source-layer)
- [Validation](#validation)
- [Repository map](#repository-map)
- [Dependencies](#dependencies)

## Mathematical setting

For $c,z\in\mathbb C$, define

$$
f_c(z)=z^2+c,\qquad f_c^0(z)=z,\qquad
f_c^{n+1}(z)=f_c(f_c^n(z)).
$$

The Mandelbrot set and the filled Julia set are

$$
\mathcal M=
\left\{
c\in\mathbb C:
\left(f_c^n(0)\right)_{n\geq 0}
\text{ is bounded}
\right\},
$$

$$
K_c=
\left\{
z\in\mathbb C:
\left(f_c^n(z)\right)_{n\geq 0}
\text{ is bounded}
\right\}.
$$

Let $G_c:\mathbb C\to\mathbb R$ be the dynamical Green function of $f_c$.
For $n\in\mathbb N$, set

$$
S_n(c)=\{z\in\mathbb C:G_c(z)<2^{-n}\},
$$

$$
\tau_c(S)=\{c+z:z\in S\},
\qquad
T_n(c)=\tau_c(S_n(c))\cap\mathcal M.
$$

The corresponding Lean objects are `MandelbrotSet`, `green_function`, and the
translated Green-sublevel sets in
[`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean).

The frozen parameter puzzle object is

```lean
ParaPuzzlePieceAt c n =
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}
```

and, for $c\in\mathcal M$, the repository proves

$$
\operatorname{ParaPuzzlePieceAt}(c,n)
=
\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}.
$$

## Formal theorem

The formalized target is local connectivity of the Mandelbrot set:

```lean
MLC.mlc_conjecture : LocallyConnectedSpace MLC.mandelbrotSet
```

The declaration contains no `sorry`. Its current proof depends on the two
project-level axioms in the next section.

## Axiom frontier

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
- MLC.residualOpenVirtualNearMoleculeAxiom
```

`Quot.sound`, `propext`, and `Classical.choice` are Lean foundations. The
project-level frontier is the following.

### A. Straddling parameter connectivity

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ⊆ MandelbrotSet)) :
    IsConnected
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ∩ MandelbrotSet)
```

Equivalently, for $c\in\mathcal M$ and $n\in\mathbb N$,

$$
\tau_c(S_n(c))\not\subseteq\mathcal M
\Longrightarrow
T_n(c)\text{ is connected}.
$$

The unrestricted translated sublevel is connected; the remaining case is its
intersection with $\mathcal M$ when the two sets straddle one another.

### B. Virtual near-Molecule renormalization

`MLC.residualOpenVirtualNearMoleculeAxiom` packages the remaining
renormalization input from Dudko's Problems 4.3 and 4.4 and Sections 4.1--4.5:

1. pseudo-Siegel a priori bounds in the remaining unbounded satellite
   quadratic-like cases;
2. a Virtual Molecule version of the Near-Degenerate Regime;
3. the infinite-renormalization interface consumed by
   [`Mlc/MainConjecture.lean`](Mlc/MainConjecture.lean).

The source is [Dudko, arXiv:2512.24171](https://arxiv.org/abs/2512.24171),
with repository copies at
[`refs/2512.24171v1.pdf`](refs/2512.24171v1.pdf) and
[`refs/2512.24171v1.txt`](refs/2512.24171v1.txt).

## Proved components

The following results are theorem-level and are not project-level axioms.

### Filled Julia sets

$$
c\in\mathcal M\Longrightarrow K_c\text{ is connected}.
$$

Formal source:
[`Mlc/FilledJuliaConnected.lean`](Mlc/FilledJuliaConnected.lean).

### Dynamical Green sublevels

$$
c\in\mathcal M\Longrightarrow S_n(c)\text{ is connected}.
$$

The proof uses connectedness of $K_c$, continuity and nonnegativity of $G_c$,
harmonicity on the basin of infinity, and the harmonic minimum principle.
Formal source:
[`Mlc/GreenSublevelConnectedDirect.lean`](Mlc/GreenSublevelConnectedDirect.lean).

### Translated sublevels

Translation by $c$ gives

$$
c\in\mathcal M\Longrightarrow
\tau_c(S_n(c))\text{ is connected}.
$$

Formal theorem: `green_sublevel_translate_connected`.

### Containment strata

The two containment cases for $T_n(c)$ are proved:

$$
\tau_c(S_n(c))\subseteq\mathcal M
\Longrightarrow
T_n(c)=\tau_c(S_n(c)),
$$

and

$$
\mathcal M\subseteq\tau_c(S_n(c))
\Longrightarrow
T_n(c)=\mathcal M.
$$

The first case uses translated-sublevel connectedness. The second uses
connectedness of $\mathcal M$ and is off the root derivation.

### Near-infinity Böttcher data

The repository contains axiom-clean local data for a parameter-dependent
Böttcher coordinate

$$
(c,z)\longmapsto\Phi_c(z)
$$

on an exterior domain, including joint continuity, parameter holomorphy,
fiber holomorphy, and a parametrized local inverse. Formal sources are under
[`Mlc/Quadratic/Complex/Bottcher/`](Mlc/Quadratic/Complex/Bottcher/).
Extending this data through the full basin and proving the finite
phase--parameter comparison remain separate obligations.

## Current discharge target

The target is to replace the frontier declaration in Section A by a theorem
with the same type:

```lean
theorem green_sublevel_translate_inter_mandelbrot_connected_straddling
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ⊆ MandelbrotSet)) :
    IsConnected
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ∩ MandelbrotSet)
```

The current non-circular route has three required steps:

1. construct finite marked Pacman or parapuzzle data and an independently
   defined realization predicate;
2. prove connectedness of the resulting parameter locus using a
   phase/component-attachment theorem or an equivalent no-separation
   argument;
3. prove the exact comparison between that locus and $T_n(c)$.

In particular, introducing connectedness as a field of the realization
structure, or replacing the frozen target by an unproved motion image, would
only restate the frontier.

## Pacman and motive bridge

The canonical bridge specification is the
[remote `main` document](https://github.com/kirill-kondrashov/raw/blob/main/bridge_between_pacman_renormalization_and_noncommutative_motives.md).
The repository keeps a concise
[audit summary](refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md).
The specification compares Pacman renormalization with BGT localizing motives
and Efimov's relative rigid motives. It explicitly treats the following as
additional constructions:

| Dynamical datum | Candidate categorical datum | Repository status |
| --- | --- | --- |
| Finite marked Pacman model | Object of a finite model category | Requires construction |
| Marked conjugacy | Morphism or equivalence of models | Requires morphism spaces |
| Boundary gluing | Exact quotient or cofiber sequence | Requires a stable model |
| Depth refinement | Exact functors between perfect categories | Requires refinement maps |
| Pacman renormalization | Exact endofunctor on the colimit category | Requires categorical renormalization |
| Marked model at depth $n$ | Parameter locus $Q_n(P)$ | Requires a realization predicate |
| MLC for $\mathcal M$ | Connected-neighborhood basis from $Q_n(P)$ | Requires a geometric theorem |

A proposed finite marked model has the form

$$
P=(f,S,G,\psi,\mathfrak m_n),
$$

where $f$ is a Pacman, $S$ is a sector, $G$ is first-return data, $\psi$ is
the gluing map, and $\mathfrak m_n$ is finite external-ray and bubble
marking. The bridge note proposes a topological model category, a spectral
enhancement, perfect modules, refinement functors, and a categorical
renormalization endofunctor.

The corresponding parameter locus is intended to be defined independently
of its topological properties:

$$
Q_n(P)=
\{c\in\mathcal M:\operatorname{Real}_n(P,c)\}.
$$

The required properties are nonemptiness, compactness, connectedness,
refinement nesting, nonempty compatible-chain intersections, and the
connected-neighborhood condition

$$
\forall c\in\mathcal M\ \forall O\subseteq\mathcal M,\quad
c\in O\text{ and }O\text{ relatively open}
\Longrightarrow
\exists n,P,\quad
c\in\operatorname{int}_{\mathcal M}Q_n(P)
\subseteq Q_n(P)\subseteq O.
$$

None of these properties has been obtained from BGT or Efimov. The exact
comparison required for the current frozen target is

$$
Q_n(P(c,n))=
\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}\cap\mathcal M.
$$

## Efimov and BGT source layer

The source-backed categorical interfaces are the universal localizing
invariant

$$
U_{\mathrm{loc}}:
\operatorname{Cat}^{\mathrm{perf}}_\infty
\longrightarrow
\operatorname{Mot}^{\mathrm{loc}},
$$

relative localizing motives over a rigid monoidal coefficient category,
duality and rigidity, relative tensor products, trace-class and nuclear
refinement, and inverse-limit or internal-Hom descriptions of morphisms.

For a finite marking group $G_P$, the proposed relative data are

$$
E_P=\operatorname{Loc}(BG_P),\qquad
M_n(P)=U_{\mathrm{loc},E_P}\bigl(\mathcal C_n(P)\bigr),
$$

where $\mathcal C_n(P)$ is the finite incidence category of the marked model.
The required separation-to-idempotent map has the form

$$
\chi_{P,n}:
C(Q_n(P),\mathbb Z)
\longrightarrow
\pi_0\operatorname{End}_{\operatorname{Mot}^{\mathrm{loc}}_{E_P}}
(M_n(P)).
$$

For every nonempty proper relatively clopen $U\subseteq Q_n(P)$, the
characteristic function $1_U$ must map to a nontrivial idempotent:

$$
\chi_{P,n}(1_U)^2=\chi_{P,n}(1_U),\qquad
\chi_{P,n}(1_U)\neq0,\qquad
\chi_{P,n}(1_U)\neq1.
$$

The selected motive must independently satisfy

$$
\neg\exists e,\quad
e^2=e\land e\neq0\land e\neq1
$$

in its endomorphism ring. This is the contradiction mechanism that would
prove connectedness of $Q_n(P)$.

The Lean interface in
[`Mlc/MotivicConnectednessFrontier.lean`](Mlc/MotivicConnectednessFrontier.lean)
records this mechanism as a proposition. It abstracts the actual relative
motive and contributes no declaration to the root axiom list. The elementary
topological obstruction is formalized in
[`Mlc/MotivicIntersectionNoGo.lean`](Mlc/MotivicIntersectionNoGo.lean):
connected ambient sets and a straddling condition do not imply connectedness
of their intersection, while a nontrivial clopen split yields a nontrivial
idempotent in $C(X,\mathbb Z)$.

The external sources are:

- [Dudko--Lyubich--Selinger, *Pacmen*](refs/1703.01206v3.pdf)
- [Blumberg--Gepner--Tabuada, *A universal characterization of higher algebraic K-theory*](https://arxiv.org/abs/1001.2282)
- [Efimov, *Rigidity of the category of localizing motives*](https://arxiv.org/abs/2510.17010)

## Validation

Run the repository checks from the root:

```bash
make build
make check
./scripts/verify_output.sh
```

## Repository map

| Component | Path |
| --- | --- |
| Root theorem | [`MLC.mlc_conjecture`](Mlc/MainConjecture.lean) |
| Axiom report | [`check_axioms.lean`](check_axioms.lean) |
| Straddling target | [`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean) |
| Motivic frontier contract | [`Mlc/MotivicConnectednessFrontier.lean`](Mlc/MotivicConnectednessFrontier.lean) |
| Topological intersection obstruction | [`Mlc/MotivicIntersectionNoGo.lean`](Mlc/MotivicIntersectionNoGo.lean) |
| Frontier overview | [`plan/PLAN_00_frontier_overview.md`](plan/PLAN_00_frontier_overview.md) |
| Parameter route | [`plan/PLAN_04_parameter_connectivity.md`](plan/PLAN_04_parameter_connectivity.md) |
| Efimov route | [`plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md`](plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md) |
| Canonical Pacman/motive bridge | [Remote `main` document](https://github.com/kirill-kondrashov/raw/blob/main/bridge_between_pacman_renormalization_and_noncommutative_motives.md) |
| Pacman/motive bridge audit | [`refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md`](refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md) |

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`.
