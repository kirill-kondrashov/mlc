# Mandelbrot Local Connectivity in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

## 1. Mathematical objects

For \(c,z\in\mathbb C\), let

\[
f_c(z)=z^2+c,\qquad f_c^0(z)=z,\qquad
f_c^{n+1}(z)=f_c(f_c^n(z)).
\]

The Mandelbrot set is

\[
\mathcal M
 =
\left\{
c\in\mathbb C:
\left(f_c^n(0)\right)_{n\geq 0}
\text{ is bounded}
\right\}.
\]

The filled Julia set of \(f_c\) is

\[
K_c
 =
\left\{
z\in\mathbb C:
\left(f_c^n(z)\right)_{n\geq 0}
\text{ is bounded}
\right\}.
\]

Let \(G_c:\mathbb C\to\mathbb R\) denote the dynamical Green function of
\(f_c\). For \(n\in\mathbb N\), define

\[
S_n(c)=\{z\in\mathbb C:G_c(z)<2^{-n}\},
\]

\[
T_n(c)
 =
\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}\cap\mathcal M.
\]

The Lean counterparts are `MandelbrotSet`, `green_function`, and the
translated Green-sublevel expressions in
`Mlc/ParaPuzzleConnectivity.lean`.

The frozen parameter puzzle object used by the current root route is

```lean
ParaPuzzlePieceAt c n =
  {c' | c' - c ∈ DynamicalPuzzlePiece c n 0}.
```

For \(c\in\mathcal M\), the repository proves the identification

\[
\operatorname{ParaPuzzlePieceAt}(c,n)
 =
\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}.
\]

## 2. Root statement

The formalized Mandelbrot local-connectivity statement is

\[
\mathcal M\text{ is locally connected}.
\]

Its Lean declaration is

```lean
MLC.mlc_conjecture : LocallyConnectedSpace MLC.mandelbrotSet
```

The declaration is proved without `sorry`; its proof depends on the two
project-level inputs listed in Section 3.

## 3. Checked axiom frontier

The current `make check` output has the following form:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
- MLC.residualOpenVirtualNearMoleculeAxiom
```

The first three declarations are Lean foundations. The project frontier is:

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

Mathematically, A asserts

\[
\neg\bigl(c+S_n(c)\subseteq\mathcal M\bigr)
\Longrightarrow
T_n(c)\text{ is connected}
\]

for every \(c\in\mathcal M\) and \(n\in\mathbb N\).

### B. Residual virtual near-Molecule input

`MLC.residualOpenVirtualNearMoleculeAxiom` packages the following
renormalization statements:

1. pseudo-Siegel a priori bounds in the remaining unbounded satellite
   quadratic-like cases;
2. the Virtual Molecule version of the Near-Degenerate Regime;
3. the implication from Problems 4.3 and 4.4 and the arguments of
   Dudko's §§4.1–4.5 to the infinite-renormalization interface consumed by
   `Mlc/MainConjecture.lean`.

The source is `refs/2512.24171v1.txt`.

## 4. Proved reductions

The following implications are theorem-level results in the repository.

### Filled Julia sets

\[
c\in\mathcal M\Longrightarrow K_c\text{ is connected}.
\]

Formal source: `Mlc/FilledJuliaConnected.lean`.

### Dynamical Green sublevels

\[
c\in\mathcal M
\Longrightarrow
S_n(c)\text{ is connected}.
\]

The proof uses connectedness of \(K_c\), continuity and nonnegativity of
\(G_c\), harmonicity on the basin of infinity, and the harmonic minimum
principle. Formal source: `Mlc/GreenSublevelConnectedDirect.lean`.

### Translated sublevels

Translation by \(c\) gives

\[
c\in\mathcal M
\Longrightarrow
\{c':G_c(c'-c)<2^{-n}\}\text{ is connected}.
\]

Formal theorem: `green_sublevel_translate_connected`.

### Nested intersection strata

The two containment cases are proved:

\[
\{c':G_c(c'-c)<2^{-n}\}\subseteq\mathcal M
\Longrightarrow
T_n(c)=\{c':G_c(c'-c)<2^{-n}\},
\]

and

\[
\mathcal M\subseteq\{c':G_c(c'-c)<2^{-n}\}
\Longrightarrow
T_n(c)=\mathcal M.
\]

The first case uses translated-sublevel connectedness. The second uses
connectedness of \(\mathcal M\) and is off the root derivation because the
corresponding theorem uses the existing `mandelbrot_set_connected` input.

Consequently, A is restricted to the intermediate straddling case.

### Analytic infrastructure

The repository contains axiom-clean near-infinity parameter Böttcher data:

\[
(c,z)\longmapsto\Phi_c(z)
\]

with joint continuity on the exterior domain, parameter holomorphy, fiber
holomorphy, and a parametrized local inverse. Formal sources are under
`Mlc/Quadratic/Complex/Bottcher/`.

This infrastructure supplies local analytic input for a future
phase–parameter construction. The finite-basin parameter-piece comparison
remains a separate theorem obligation.

## 5. Exact goal for A

The target theorem is the declaration in Section 3A with `axiom` replaced by
`theorem`. The current plan uses a finite parameter realization
\(Q_n(P(c,n))\), defined from finite marked Pacman or parapuzzle data without
an `IsConnected` field.

The exact comparison required for the frozen root target is

\[
Q_n(P(c,n))
 =
\{c'\in\mathbb C:G_c(c'-c)<2^{-n}\}\cap\mathcal M.
\tag{5.1}
\]

The connectedness mechanism is categorical. For a finite marking group
\(G_P\), let

\[
E_P=\operatorname{Loc}(BG_P)
\]

be the rigid convolution coefficient category, let \(\mathcal C_n(P)\) be
the finite idempotent-complete stable incidence category, and set

\[
M_n(P)
 =
U_{\mathrm{loc},E_P}\bigl(\mathcal C_n(P)\bigr)
\in \operatorname{Mot}^{\mathrm{loc}}_{E_P}.
\]

The required conservative realization is a morphism

\[
\chi_{P,n}:
C\bigl(Q_n(P),\mathbb Z\bigr)
\longrightarrow
\pi_0\operatorname{End}_{\operatorname{Mot}^{\mathrm{loc}}_{E_P}}
(M_n(P)).
\tag{5.2}
\]

For every nonempty proper relatively clopen
\(U\subseteq Q_n(P)\), the characteristic function \(1_U\) must satisfy

\[
\chi_{P,n}(1_U)^2=\chi_{P,n}(1_U),\qquad
\chi_{P,n}(1_U)\neq 0,\qquad
\chi_{P,n}(1_U)\neq 1.
\tag{5.3}
\]

The selected motive must satisfy

\[
\neg\exists e\in
\pi_0\operatorname{End}_{\operatorname{Mot}^{\mathrm{loc}}_{E_P}}(M_n(P)):
\quad
e^2=e\ \land\ e\neq0\ \land\ e\neq1.
\tag{5.4}
\]

Equations (5.2)–(5.4) give

\[
Q_n(P)\text{ disconnected}
\Longrightarrow
\text{a nontrivial idempotent of }
\pi_0\operatorname{End}(M_n(P))
\Longrightarrow\bot,
\]

so \(Q_n(P)\) is connected. Equation (5.1) then proves A.

## 6. Lean categorical frontier contract

The category-theoretic interface is recorded in
`Mlc/MotivicConnectednessFrontier.lean`.

```lean
MLC.Motivic.GreenSublevelStraddlingMotivicFrontier : Prop
```

Its payload

```lean
MLC.Motivic.SeparationReflectingIndecomposable
```

contains:

```text
characteristic :
  C(Q, ℤ) →* EndM

reflects_clopen :
  nontrivial clopen U ⊆ Q
    → characteristic (1_U) is a nontrivial idempotent

indecomposable :
  EndM has no nontrivial idempotent.
```

`EndM` is a ring-level abstraction for
\(\pi_0\operatorname{End}_{\operatorname{Mot}^{\mathrm{loc}}_{E_P}}(M_n(P))\).
The file proves the conditional implication from this contract to the
straddling connectivity conclusion. Instantiating `EndM` with an actual
Efimov relative motive, constructing \(Q_n(P)\), and proving (5.1) remain
open implementation goals. The contract contributes no declaration to the
root axiom list.

The topological separation test in
`Mlc/MotivicIntersectionNoGo.lean` proves that connectedness of two ambient
sets and a straddling condition alone supply no intersection theorem. It also
proves that a nontrivial clopen split yields a nontrivial idempotent in
\(C(X,\mathbb Z)\).

## 7. Efimov source layer

The motivic plan uses:

\[
U_{\mathrm{loc}}:\operatorname{Cat}^{\mathrm{perf}}
\longrightarrow\operatorname{Mot}^{\mathrm{loc}},
\]

the universal finitary localizing invariant, together with the following
source results from Efimov, arXiv:2510.17010v1:

- rigidity of \(\operatorname{Mot}^{\mathrm{loc}}\);
- dualizability and rigidity of relative
  \(\operatorname{Mot}^{\mathrm{loc}}_E\) over a rigid monoidal base;
- eventual trace-class characterizations of nuclear ind-systems;
- inverse-limit and internal-Hom descriptions of morphisms from nuclear or
  proper sources;
- equivariant and local-system variants, including product decompositions over
  disconnected bases.

These results provide the refinement, duality, and endomorphism framework in
(5.2)–(5.4). The finite phase–parameter realization, conservativity of
\(\chi_{P,n}\), motive indecomposability, and comparison (5.1) require
separate proofs.

The source files are kept in the canonical raw reference directory:

```text
/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.pdf
/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.tex
```

## 8. Root dependency structure

The current theorem path has the form

\[
\begin{aligned}
\texttt{MLC.mlc\_conjecture}
&\Leftarrow
\text{finite/primitive branch data}
+\text{satellite renormalization data}\\
&\Leftarrow
\text{A}
+\text{B}.
\end{aligned}
\]

The Molecule dependency is pinned in `lake-manifest.json` at
`385fc36c553947cf125d09848c2a3077fc751209`.

## 9. Validation commands

```bash
make build
make check
./scripts/verify_output.sh
```

The expected project-level axiom names are exactly the two declarations in
Section 3.

## 10. Repository entry points

- Root theorem: [`MLC.mlc_conjecture`](Mlc/MainConjecture.lean)
- Axiom report: [`check_axioms.lean`](check_axioms.lean)
- Straddling target: [`Mlc/ParaPuzzleConnectivity.lean`](Mlc/ParaPuzzleConnectivity.lean)
- Categorical contract:
  [`Mlc/MotivicConnectednessFrontier.lean`](Mlc/MotivicConnectednessFrontier.lean)
- Topological motivic gate:
  [`Mlc/MotivicIntersectionNoGo.lean`](Mlc/MotivicIntersectionNoGo.lean)
- Frontier overview: [`plan/PLAN_00_frontier_overview.md`](plan/PLAN_00_frontier_overview.md)
- Parameter route: [`plan/PLAN_04_parameter_connectivity.md`](plan/PLAN_04_parameter_connectivity.md)
- Efimov route: [`plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md`](plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md)
- Dudko source: [`refs/2512.24171v1.txt`](refs/2512.24171v1.txt)

## 11. Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`.
