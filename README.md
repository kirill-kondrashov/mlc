# Mandelbrot Local Connectivity in Lean 4

[![Lean CI](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository contains a Lean 4 formalization of the Mandelbrot
local-connectivity target with an explicit, conditional root input.

## Current mathematical target

Let

$$
f_c(z)=z^2+c,\qquad
p_0(c)=0,\qquad
p_{n+1}(c)=f_c(p_n(c)).
$$

The formal Mandelbrot set is

$$
M
=\left\{c\in\mathbb C:
  \exists B\in\mathbb R\ \forall n\in\mathbb N,\
  \lVert p_n(c)\rVert\le B
\right\}
=\bigcap_{n\in\mathbb N}
  \left\{c:\lVert p_n(c)\rVert\le2\right\}.
$$

The target is

$$
\mathrm{MLC}(M)
:=\mathrm{LocallyConnectedSpace}(M).
$$

The categorical target is definitionally equivalent:

```lean
MLC.Categorical.MLCConjecture
  ↔ LocallyConnectedSpace MLC.mandelbrotSet
```

The public root has no `GreenSublevelIntersectionCategoricalData` hypothesis.

## Root input and exact frontier

For $N\in\mathbb N$, define the finite critical-orbit outer stage

$$
O_N
:=\left\{c:
  \lVert c\rVert\le2\ \land\
  \forall n\le N,\ \lVert p_n(c)\rVert\le2
  \right\}.
$$

The following are proved:

$$
\begin{aligned}
&M\subseteq O_N,\\
&N\le L\Longrightarrow O_L\subseteq O_N,\\
&O_N\text{ is compact},\\
&\bigcap_{N\in\mathbb N}O_N=M.
\end{aligned}
$$

For $x\in M$, $r>0$, and $N\in\mathbb N$, write

$$
C_N(x,r)
:=\operatorname{Comp}_{x}
  \left(O_N\cap\overline B(x,r)\right).
$$

The root-facing finite-stage buffer predicate is

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

The root input is the proposition

```lean
structure MLC.RootInput : Prop where
  uniformOuterBuffer :
    MLC.ParameterComponent.MandelbrotUniformOuterBuffer
```

Mathematically, `MLC.RootInput` is exactly the packaged proposition
$\mathrm{BUF}(M,O)$. The proved root implication is

$$
\boxed{
\mathrm{BUF}(M,O)
\Longrightarrow
\mathrm{MLC.RootInput}
\Longrightarrow
\mathrm{MLC}(M).
}
$$

The public declarations are:

```lean
MLC.Categorical.categorical_mlc_conjecture :
  MLC.RootInput → MLC.Categorical.MLCConjecture

MLC.mlc_conjecture :
  MLC.RootInput → LocallyConnectedSpace MLC.mandelbrotSet
```

No inhabitant of `MLC.RootInput` or $\mathrm{BUF}(M,O)$ is currently
provided. Therefore the repository does not prove $\mathrm{MLC}(M)$
unconditionally.

## Implemented current-state interfaces

| Module | Current theorem-level content | Remaining input |
| --- | --- | --- |
| `Mlc/CategoricalMandelbrot.lean` | Compact decreasing outer stages and increasing bounded-orbit inner stages with exact limits equal to $M$. | No finite-stage connectedness theorem is assumed. |
| `Mlc/ParameterComponentApproximation.lean` | Components of metric balls; $\mathrm{BUF}(M,O)\Rightarrow\mathrm{MLC}(M)$. | No inhabitant of $\mathrm{BUF}(M,O)$. |
| `Mlc/CertifiedOrbitApproximation.lean` | Finite compact-cell outer systems with $\bigcap_N E_N=M$. | A nontrivial dyadic, interval, CAD, or semialgebraic cell generator. |
| `Mlc/CertifiedTrappingRegions.lean` | Rational-box trapping certificates imply parameter-box inclusion in $M$. | Inner density. |
| `Mlc/ParameterClassification.lean` | Least escape time outside $M$ and an exhaustive priority classification with a retained residual class. | Class-specific component estimates and decidability are not asserted. |
| `Mlc/ParameterAddressSpace.lean` | Nonempty nested address intersections and singleton uniqueness under vanishing diameter. | Address coverage and vanishing diameter for a concrete generator. |
| `Mlc/FiniteComponentCriterion.lean` | Finite local-piece certificates imply $\mathrm{BUF}(M,O)$ and hence `MLC.RootInput`. | A finite-component certificate is not supplied. |
| `Mlc/FlowInterfaces.lean` | Uniform-limit parametrization and terminal radial-extension structures. | No flow construction or flow-to-MLC theorem is asserted. |

## Explicit unresolved propositions

### Finite component route

The implemented finite-component proposition has the form

$$
\begin{aligned}
\mathrm{FC}:\Longleftrightarrow
\forall k\ \exists\text{ finite }J,\ T,\
\{(P_i,r_i,\delta_i)\}_{i\in J}:\quad
&0<\delta_i<r_i<2^{-k}\quad(i\in J),\\
&O_T\subseteq\bigcup_{i\in J}P_i,\\
&\forall i\in J\ \forall c\in M\cap P_i\ \forall N\ \exists L\ge N:\\
&\qquad O_L\cap\overline B(c,\delta_i)
\subseteq C_N(c,r_i).
\end{aligned}
$$

The proved implication is

$$
\mathrm{FC}
\Longrightarrow
\mathrm{BUF}(M,O)
\Longrightarrow
\mathrm{MLC}(M).
$$

The repository contains no proof of $\mathrm{FC}$.

### Certified inner route

For a finite increasing family $F=(F_N)_{N\in\mathbb N}$ of rational
trapping certificates, define

$$
I_N(F):=\bigcup_{\tau\in F_N}P_\tau.
$$

The proved properties are

$$
I_N(F)\subseteq M,\qquad
N\le L\Longrightarrow I_N(F)\subseteq I_L(F).
$$

The missing density statement is

$$
\mathrm{ID}(F):\Longleftrightarrow
\forall c\in M\ \forall\varepsilon>0\
\exists N\ \exists x\in I_N(F),\ d(x,c)<\varepsilon.
$$

Under this proposition,

$$
\mathrm{ID}(F)
\Longrightarrow
\overline{\bigcup_N I_N(F)}=M.
$$

No family with a proved instance of $\mathrm{ID}(F)$ is supplied.

### Address route

For a finite-cell system $E=(Q_{N,i})$, an address
$a=(a_N)_{N\in\mathbb N}$ satisfies

$$
Q_{N+1,a_{N+1}}\subseteq Q_{N,a_N}.
$$

The proved compactness statement is

$$
\bigcap_N Q_{N,a_N}\ne\varnothing.
$$

Under the explicit vanishing-diameter proposition

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

the intersection is a singleton. Coverage remains the separate obligation

$$
\mathrm{AC}(E):\Longleftrightarrow
\forall c\in M\ \exists a\ \forall N,\ c\in Q_{N,a_N}.
$$

No concrete generator is currently shown to satisfy both $\mathrm{VD}(E)$
and $\mathrm{AC}(E)$.

### Flow route

A coherent parametrization consists of continuous maps

$$
h_N:\overline{\mathbb D}\to\mathbb C,\qquad
h:\overline{\mathbb D}\to\mathbb C
$$

with $h_N(\overline{\mathbb D})\subseteq S$, uniform convergence
$h_N\to h$, and surjectivity $h(\overline{\mathbb D})=S$. The implemented
limit theorem proves the range equality from the stated fields.

A terminal radial-extension certificate is a continuous map

$$
H:[1,e]\times\mathbb C\to\mathbb C
$$

such that

$$
\begin{aligned}
&H([1,e]\times\mathbb C)\subseteq A,\\
&H(1,x)\in S\quad(x\in\mathbb C),\\
&H(1,x)=x\quad(x\in S).
\end{aligned}
$$

These are explicit interfaces only. No theorem currently derives
$\mathrm{MLC}(M)$ from either interface.

## Current status

$$
\boxed{
\mathrm{FC}
\Longrightarrow
\mathrm{BUF}(M,O)
\Longrightarrow
\mathrm{RootInput}
\Longrightarrow
\mathrm{MLC}(M)
}
$$

The current unproved existence obligations are

$$
\mathrm{FC},\qquad
\mathrm{BUF}(M,O),\qquad
\exists F\,\mathrm{ID}(F),\qquad
\exists E\,(\mathrm{VD}(E)\land\mathrm{AC}(E)),
\qquad
\mathrm{RootFlowInput}(M).
$$

These are propositions or certificate structures, not project-level axioms.
The repository does not assert any of them globally.

The supported root axiom frontier is

$$
\operatorname{Axioms}(\text{root})
=\{\mathrm{propext},\mathrm{Quot.sound},\mathrm{Classical.choice}\}.
$$

There is no project-level `axiom`, no `sorryAx`, and no unconditional MLC
theorem.

## Validation

```bash
make build
make check
./scripts/verify_output.sh
```

## Main files

| Purpose | Path |
| --- | --- |
| Public import root | [`Mlc.lean`](Mlc.lean) |
| Categorical root | [`Mlc/CategoricalRoot.lean`](Mlc/CategoricalRoot.lean) |
| Compatibility theorem | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Outer-buffer theorem | [`Mlc/ParameterComponentApproximation.lean`](Mlc/ParameterComponentApproximation.lean) |
| Finite outer certificates | [`Mlc/CertifiedOrbitApproximation.lean`](Mlc/CertifiedOrbitApproximation.lean) |
| Inner trapping certificates | [`Mlc/CertifiedTrappingRegions.lean`](Mlc/CertifiedTrappingRegions.lean) |
| Parameter classification | [`Mlc/ParameterClassification.lean`](Mlc/ParameterClassification.lean) |
| Address interface | [`Mlc/ParameterAddressSpace.lean`](Mlc/ParameterAddressSpace.lean) |
| Finite-component bridge | [`Mlc/FiniteComponentCriterion.lean`](Mlc/FiniteComponentCriterion.lean) |
| Flow interfaces | [`Mlc/FlowInterfaces.lean`](Mlc/FlowInterfaces.lean) |
| Axiom checker | [`check_axioms.lean`](check_axioms.lean) |

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4)
- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.28.0`.
