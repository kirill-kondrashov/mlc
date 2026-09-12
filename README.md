# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

Lean 4 formalisation of the Mandelbrot local-connectivity target with an
explicit root hypothesis.

## Formal target

$$
f_c(z)=z^2+c,\qquad
p_0(c)=0,\qquad
p_{n+1}(c)=f_c(p_n(c)).
$$

$$
M
=\left\{c\in\mathbb C:
  \exists B\in\mathbb R\ \forall n\in\mathbb N,\
  \lVert p_n(c)\rVert\le B
\right\}
=\bigcap_{n\in\mathbb N}
  \left\{c:\lVert p_n(c)\rVert\le2\right\}.
$$

$$
\mathrm{MLC}(M):=\mathrm{LocallyConnectedSpace}(M).
$$

The categorical target satisfies

```lean
MLC.Categorical.MLCConjecture
  ↔ LocallyConnectedSpace MLC.mandelbrotSet
```

## Root input

For $N\in\mathbb N$, define

$$
O_N
:=\left\{c:
  \lVert c\rVert\le2\ \land\
  \forall n\le N,\ \lVert p_n(c)\rVert\le2
  \right\}.
$$

The formalisation proves

$$
\begin{aligned}
&M\subseteq O_N,\\
&N\le L\Longrightarrow O_L\subseteq O_N,\\
&\forall N,\ O_N\text{ is compact},\\
&\bigcap_N O_N=M.
\end{aligned}
$$

For $x\in M$, $r>0$, and $N\in\mathbb N$, let

$$
C_N(x,r):=\operatorname{Comp}_{x}
  \left(O_N\cap\overline B(x,r)\right).
$$

The root proposition is

$$
\begin{aligned}
\mathrm{BUF}(M,O):\Longleftrightarrow
\forall x\in M\ \forall\varepsilon>0\ \exists r,\delta\in\mathbb R:\quad
&0<\delta<r<\varepsilon\\
&{}\land
\forall N\ \exists L\ge N:
O_L\cap\overline B(x,\delta)
\subseteq C_N(x,r).
\end{aligned}
$$

Its Lean packaging is

```lean
structure MLC.RootInput : Prop where
  uniformOuterBuffer :
    MLC.ParameterComponent.MandelbrotUniformOuterBuffer
```

The root theorems are

```lean
MLC.Categorical.categorical_mlc_conjecture :
  MLC.RootInput → MLC.Categorical.MLCConjecture

MLC.mlc_conjecture :
  MLC.RootInput → LocallyConnectedSpace MLC.mandelbrotSet
```

The formal implication chain is

$$
\mathrm{BUF}(M,O)
\Longrightarrow
\mathrm{RootInput}
\Longrightarrow
\mathrm{MLC}(M).
$$

The repository supplies no global instance of $\mathrm{BUF}(M,O)$.

## Implemented interfaces

### Finite outer systems

A finite-cell system provides finite index types $I_N$ and nonempty compact
cells $Q_{N,i}$ with

$$
E_N:=\bigcup_{i\in I_N}Q_{N,i},
$$

$$
\begin{aligned}
&N\le L\Longrightarrow E_L\subseteq E_N,\\
&M\subseteq E_N,\\
&x\in Q_{N,i}\Longrightarrow
  \exists y\in O_N,\ d(x,y)\le2^{-N}.
\end{aligned}
$$

The proved limit theorem is

$$
\forall N,\ E_N\text{ is compact},
\qquad
\bigcap_N E_N=M.
$$

The exact baseline $I_N=\{\ast\}$, $Q_{N,\ast}=O_N$ is implemented.
Construction of a nontrivial dyadic, interval, CAD, or semialgebraic system
remains open.

### Finite inner systems

A finite-union trapping certificate has a rational parameter rectangle
$P_\tau$, a finite union $U_\tau$ of rational rectangles, and a bound
$B_\tau$, satisfying

$$
\begin{aligned}
&0\in U_\tau,\\
&\forall c\in P_\tau\ \forall z\in U_\tau,\ f_c(z)\in U_\tau,\\
&\forall z\in U_\tau,\ \lVert z\rVert\le B_\tau.
\end{aligned}
$$

The proved soundness theorem is

$$
\tau\text{ is certified}\Longrightarrow P_\tau\subseteq M.
$$

For an increasing finite family $F=(F_N)_N$, define

$$
I_N(F):=\bigcup_{\tau\in F_N}P_\tau.
$$

The formalisation proves

$$
I_N(F)\subseteq M,\qquad
N\le L\Longrightarrow I_N(F)\subseteq I_L(F).
$$

The unresolved density proposition is

$$
\mathrm{ID}(F):\Longleftrightarrow
\forall c\in M\ \forall\varepsilon>0\
\exists N\ \exists x\in I_N(F),\ d(x,c)<\varepsilon.
$$

It implies

$$
\overline{\bigcup_N I_N(F)}=M.
$$

The single-rectangle scheme in `CertifiedTrappingRegions.lean` satisfies
$|\operatorname{Re}c|\le1/2$ for every certified parameter, so its
`InnerDensity` proposition is false. Finite unions admit a certificate for
the parameter box centered at $-1$ with real and imaginary halfwidth
$1/256$; this is an instance of `FiniteTrappingRegions.lean`.

### Addresses and classification

An address $a=(a_N)_N$ satisfies

$$
Q_{N+1,a_{N+1}}\subseteq Q_{N,a_N}.
$$

The nested intersection is nonempty. Under

$$
\begin{aligned}
\mathrm{VD}(E):\Longleftrightarrow
\forall a\ \forall x,y\in\mathbb C:\quad
&\left(\forall N,\ x\in Q_{N,a_N}\right)
\land\left(\forall N,\ y\in Q_{N,a_N}\right)\\
&\Longrightarrow
\forall\varepsilon>0,\ d(x,y)<\varepsilon,
\end{aligned}
$$

it is a singleton. Address coverage is the separate proposition

$$
\mathrm{AC}(E):\Longleftrightarrow
\forall c\in M\ \exists a\ \forall N,\ c\in Q_{N,a_N}.
$$

For the dynamical classification, the formalisation proves

$$
c\notin M\Longleftrightarrow
\exists n,\ \lVert p_n(c)\rVert>2,
$$

with a least escape time. It also proves an exhaustive priority partition

$$
\forall c,\quad
D_0(c)\lor D_1(c)\lor D_2(c)\lor D_3(c)\lor D_4(c)\lor D_5(c),
$$

where the classes are attracting, parabolic, Siegel, Cremer, eventually
periodic, and residual. The residual class remains present in the formal
partition.

### Finite-component bridge

Here $P_i$ are rational closed rectangles, $r_i,\delta_i\in\mathbb R$,
and $k,T,N,L\in\mathbb N$. The finite-component proposition is

$$
\begin{aligned}
\mathrm{FC}:\Longleftrightarrow
\forall k\ \exists\text{ finite }J,\ T,\
\{(P_i,r_i,\delta_i)\}_{i\in J}:\quad
&\forall i\in J,\quad 0<\delta_i<r_i<2^{-k},\\
&O_T\subseteq\bigcup_{i\in J}P_i,\\
&\forall i\in J\ \forall c\in M\cap P_i\ \forall N\ \exists L\ge N:\\
&\qquad O_L\cap\overline B(c,\delta_i)
\subseteq C_N(c,r_i).
\end{aligned}
$$

The proved bridge is

$$
\mathrm{FC}\Longrightarrow\mathrm{BUF}(M,O)
\Longrightarrow\mathrm{RootInput}
\Longrightarrow\mathrm{MLC}(M).
$$

The repository contains no proof of $\mathrm{FC}$.

### Uniform geometric reduction

[Proof document (PDF)](docs/uniform_geometric_mlc.pdf) ·
[LaTeX source](docs/uniform_geometric_mlc.tex).

Let $D=[-2,2]+i[-2,2]$. The hypothesis $\mathrm{UG}$ asserts the
existence of continuous maps $R_n:D\to D$ and integers $N_n\ge n$ such that

$$
\begin{aligned}
&R_0=\operatorname{id}_D,\qquad R_n|_{O_{N_n}}=\operatorname{id},\\
&\forall z\in D\ \exists w\in O_{N_n},\quad |R_n(z)-w|\le2^{-n},\\
&\|R_{n+1}-R_n\|_\infty\le8\,2^{-n}.
\end{aligned}
$$

The proved reduction yields a continuous limit $R:D\to M$ satisfying

$$
\|R_n-R\|_\infty\le16\,2^{-n},\qquad R|_M=\operatorname{id}_M.
$$

Images of convex neighborhoods under $R$ give

$$
\mathrm{UG}\Longrightarrow\text{a continuous retraction }D\to M
\Longrightarrow\mathrm{MLC}(M).
$$

The PDF proves the uniform-limit retraction theorem and its
local-connectivity consequence. Existence of an infinite compatible
tower remains unproved.

The Lean formalisation of the implication is

```lean
MLC.UniformGeometry.mandelbrot_locallyConnected_of_squareTower
  (T : MLC.UniformGeometry.OrbitRetractionTower
    MLC.UniformGeometry.parameterSquare) :
  LocallyConnectedSpace MLC.mandelbrotSet
```

## Current obligations

The remaining existence statements are

$$
\mathrm{UG},\qquad \mathrm{BUF}(M,O),\qquad
\mathrm{FC},\qquad
\exists F\,\mathrm{ID}(F),\qquad
\exists E\,(\mathrm{VD}(E)\land\mathrm{AC}(E)).
$$

Here $F$ uses finite-union trapping certificates. These existence statements
remain explicit obligations; the single-rectangle density statement has a
proved negation.

The root axiom frontier is

$$
\operatorname{Axioms}(\text{root})
=\{\mathrm{propext},\mathrm{Quot.sound},\mathrm{Classical.choice}\}.
$$

The source contains no project-level `axiom`, no `sorryAx`, and no
unconditional theorem of $\mathrm{MLC}(M)$.

## Validation

```bash
make build
make check
./scripts/verify_output.sh
make check-uniform
make proof-pdf
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
```

This summary concerns `MLC.RootInput → LocallyConnectedSpace M`; it
does not supply the `MLC.RootInput` argument.

## Main files

| Purpose | Path |
| --- | --- |
| Public import root | [`Mlc.lean`](Mlc.lean) |
| Categorical root | [`Mlc/CategoricalRoot.lean`](Mlc/CategoricalRoot.lean) |
| Compatibility theorem | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Outer-buffer theorem | [`Mlc/ParameterComponentApproximation.lean`](Mlc/ParameterComponentApproximation.lean) |
| Finite outer systems | [`Mlc/CertifiedOrbitApproximation.lean`](Mlc/CertifiedOrbitApproximation.lean) |
| Finite-union trapping systems | [`Mlc/FiniteTrappingRegions.lean`](Mlc/FiniteTrappingRegions.lean) |
| Single-rectangle obstruction | [`Mlc/TrappingRegionObstruction.lean`](Mlc/TrappingRegionObstruction.lean) |
| Parameter classification | [`Mlc/ParameterClassification.lean`](Mlc/ParameterClassification.lean) |
| Address interface | [`Mlc/ParameterAddressSpace.lean`](Mlc/ParameterAddressSpace.lean) |
| Finite-component bridge | [`Mlc/FiniteComponentCriterion.lean`](Mlc/FiniteComponentCriterion.lean) |
| Flow interfaces | [`Mlc/FlowInterfaces.lean`](Mlc/FlowInterfaces.lean) |
| Fixed geometric domain | [`Mlc/UniformGeometricDomain.lean`](Mlc/UniformGeometricDomain.lean) |
| Uniform limit estimates | [`Mlc/UniformGeometricApproximation.lean`](Mlc/UniformGeometricApproximation.lean) |
| Retraction and local connectedness | [`Mlc/RetractionLocalConnectivity.lean`](Mlc/RetractionLocalConnectivity.lean) |
| Geometric theorem assembly | [`Mlc/UniformGeometricRoot.lean`](Mlc/UniformGeometricRoot.lean) |
| Axiom checker | [`check_axioms.lean`](check_axioms.lean) |
| Geometric theorem audit | [`check_uniform_program.lean`](check_uniform_program.lean) |

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.28.0`.
