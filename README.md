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

The public root contains no `GreenSublevelIntersectionCategoricalData`
field.

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

A rational trapping certificate $\tau=(P_\tau,U_\tau,B_\tau)$ satisfies

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

The finite-component certificate proposition has the form

$$
\begin{aligned}
\mathrm{FC}:\Longleftrightarrow
\forall k\ \exists\text{ finite }J,\ T,\
\{(P_i,r_i,\delta_i)\}_{i\in J}:\quad
&0<\delta_i<r_i<2^{-k},\\
&O_T\subseteq\bigcup_{i\in J}P_i,\\
&\forall i,c\in M\cap P_i,\ \forall N\ \exists L\ge N:\\
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

### Parametrisation and flow

A coherent parametrisation consists of continuous maps

$$
h_N:\overline{\mathbb D}\to\mathbb C,\qquad
h:\overline{\mathbb D}\to\mathbb C,
$$

with $h_N(\overline{\mathbb D})\subseteq S$, uniform convergence
$h_N\to h$, and $h(\overline{\mathbb D})=S$. The range equality is proved
from the stated fields.

A terminal extension is a continuous map

$$
H:[1,e]\times\mathbb C\to\mathbb C
$$

with

$$
\begin{aligned}
&H([1,e]\times\mathbb C)\subseteq A,\\
&H(1,x)\in S\quad(x\in\mathbb C),\\
&H(1,x)=x\quad(x\in S).
\end{aligned}
$$

These structures carry no theorem deriving $\mathrm{MLC}(M)$.

## Current obligations

The remaining existence statements are

$$
\mathrm{BUF}(M,O),\qquad
\mathrm{FC},\qquad
\exists F\,\mathrm{ID}(F),\qquad
\exists E\,(\mathrm{VD}(E)\land\mathrm{AC}(E)),
\qquad
\mathrm{RootFlowInput}(M).
$$

They occur as theorem hypotheses or certificate fields. The project declares
no global instance for any of them.

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
```

## Main files

| Purpose | Path |
| --- | --- |
| Public import root | [`Mlc.lean`](Mlc.lean) |
| Categorical root | [`Mlc/CategoricalRoot.lean`](Mlc/CategoricalRoot.lean) |
| Compatibility theorem | [`Mlc/Core.lean`](Mlc/Core.lean) |
| Outer-buffer theorem | [`Mlc/ParameterComponentApproximation.lean`](Mlc/ParameterComponentApproximation.lean) |
| Finite outer systems | [`Mlc/CertifiedOrbitApproximation.lean`](Mlc/CertifiedOrbitApproximation.lean) |
| Inner trapping systems | [`Mlc/CertifiedTrappingRegions.lean`](Mlc/CertifiedTrappingRegions.lean) |
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
