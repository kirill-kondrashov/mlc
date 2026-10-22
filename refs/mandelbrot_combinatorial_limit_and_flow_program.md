# Mandelbrot set: certified limits, classification, and deformation

## 0. Status and target

| Label | Meaning |
| --- | --- |
| **R** | Existing repository theorem |
| **I** | Implemented Lean declaration proved from explicit fields |
| **D** | Mathematical deduction with proof below; Lean formalization pending |
| **T** | Classical theorem; Lean implementation not asserted |
| **O** | Proof obligation; neither theorem nor axiom |

\[
\boxed{
  \text{finite certificates}
  \ \longrightarrow\
  \text{uniform component control}
  \ \longrightarrow\
  \mathrm{MLC.RootInput}
  \ \longrightarrow\
  \operatorname{LocallyConnected}(M)
}
\tag{0.1}
\]

\[
\operatorname{Axioms}_{\mathrm{new}}=\varnothing.
\tag{0.2}
\]

\[
\begin{array}{c|c}
\text{Implemented interface} & \text{Lean module} \\
\hline
\text{finite compact outer stages and exact limit} &
\texttt{Mlc/CertifiedOrbitApproximation.lean} \\
\text{rational-box trapping certificates} &
\texttt{Mlc/CertifiedTrappingRegions.lean} \\
\text{escape and retained priority classification} &
\texttt{Mlc/ParameterClassification.lean} \\
\text{nested address compactness and uniqueness} &
\texttt{Mlc/ParameterAddressSpace.lean} \\
\text{finite-component-to-BUF implication} &
\texttt{Mlc/FiniteComponentCriterion.lean} \\
\text{uniform-limit and terminal-extension interfaces} &
\texttt{Mlc/FlowInterfaces.lean}
\end{array}
\tag{0.3}
\]

\[
\text{No inhabitant is supplied for (O-QE), (O-IN), (O-CLASS), (O-FC),
(O-PARAM), or (O-RAD).}
\tag{0.4}
\]

## 1. Definitions

\[
\begin{aligned}
f_c(z)&=z^2+c,
&
p_0(c)&=0,
&
p_{n+1}(c)&=p_n(c)^2+c,
\\
M&=\{c\in\mathbb C:\sup_{n\ge0}|p_n(c)|<\infty\},
&
D&=[-2,2]+i[-2,2].
\end{aligned}
\tag{1.1}
\]

**R. Escape-radius identity.**

\[
M=\bigcap_{n\ge0}\{c:|p_n(c)|\le2\}
\subseteq\overline B(0,2)\subseteq D.
\tag{1.2}
\]

**Conventions.**

\[
\begin{aligned}
A^{+\eta}&=\{z:\operatorname{dist}(z,A)\le\eta\},
\\
d_H(A,B)&=
\max\{\sup_{a\in A}\operatorname{dist}(a,B),
       \sup_{b\in B}\operatorname{dist}(b,A)\},
\\
\operatorname{Comp}(F,x)&=
\text{the connected component of \(F\) containing \(x\)},\qquad x\in F.
\end{aligned}
\tag{1.3}
\]

\[
d_H(A,B)\text{ used only for nonempty compact }A,B.
\tag{1.4}
\]

## 2. Exact outer stages

**Definition.**

\[
O_N=
\left\{
c\in\mathbb C:
|c|^2\le4\ \land\
\bigwedge_{0\le n\le N}|p_n(c)|^2\le4
\right\}.
\tag{2.1}
\]

**R.**

\[
0\in M\subseteq O_{N+1}\subseteq O_N\subseteq\overline B(0,2),
\qquad
O_N\text{ compact},
\qquad
\bigcap_NO_N=M.
\tag{2.2}
\]

**D. Polynomial presentation.**

\[
\begin{aligned}
p_n(x+iy)&=a_n(x,y)+ib_n(x,y),\\
a_0=b_0&=0,\\
a_{n+1}&=a_n^2-b_n^2+x,\\
b_{n+1}&=2a_nb_n+y,\\
a_n,b_n&\in\mathbb Z[x,y].
\end{aligned}
\tag{2.3}
\]

\[
O_N=
\left\{(x,y):
x^2+y^2\le4\ \land\
\bigwedge_{n\le N}(a_n^2+b_n^2\le4)
\right\}.
\tag{2.4}
\]

**T. Finite algebraic decision interface.**

\[
\begin{gathered}
\operatorname{RCFDecide}:
\operatorname{ClosedFirstOrderFormula}(\mathbb Q,+,\cdot,\le)
\longrightarrow\{\mathsf{true},\mathsf{false}\},\\
\forall\varphi,\qquad
\operatorname{RCFDecide}(\varphi)=\mathsf{true}
\iff\mathbb R\models\varphi.
\end{gathered}
\tag{2.5}
\]

**O-QE.** A terminating implementation of (2.5), together with a Lean
soundness theorem; alternatively, a terminating certificate generator and
a Lean-verified certificate checker.

\[
\text{Numerical sampling}\ne\operatorname{RCFDecide}.
\tag{2.6}
\]

## 3. Finite cubical outer approximants

**Definitions.**

\[
\begin{aligned}
h_n&=2^{-n},\\
Q_{n,a,b}
&=[-2+ah_n,-2+(a+1)h_n]\\
&\hspace{1.5em}
+i[-2+bh_n,-2+(b+1)h_n],\\
\mathcal Q_n
&=\{Q_{n,a,b}:0\le a,b<4\cdot2^n\},\\
V_n&=\{Q\in\mathcal Q_n:Q\cap O_n\ne\varnothing\},\\
E_n&=\bigcup_{Q\in V_n}Q.
\end{aligned}
\tag{3.1}
\]

**Finite membership test.**

\[
Q\in V_n
\iff
\mathbb R\models
\exists x\,\exists y\,
\bigl((x,y)\in Q\land(x,y)\in O_n\bigr).
\tag{3.2}
\]

**D. Outer-limit theorem.**

\[
\boxed{
M\subseteq O_n\subseteq E_n,\qquad
E_{n+1}\subseteq E_n,\qquad
\bigcap_nE_n=M.
}
\tag{3.3}
\]

**Proof.**

\[
\begin{aligned}
Q'\in V_{n+1},\ Q' \subseteq Q\in\mathcal Q_n
&\Longrightarrow Q\cap O_n\ne\varnothing,\\
E_n&\subseteq O_n^{+\sqrt2\,h_n}.
\end{aligned}
\tag{3.4}
\]

For \(x\in\bigcap_nE_n\), choose \(y_n\in O_n\) with
\(|x-y_n|\le\sqrt2\,h_n\). Then

\[
\forall k\ \forall n\ge k,\quad y_n\in O_k,
\qquad
y_n\longrightarrow x,
\qquad
O_k\text{ closed}
\Longrightarrow x\in\bigcap_kO_k=M.
\tag{3.5}
\]

**D. Qualitative Hausdorff convergence.**

\[
d_H(O_n,M)\longrightarrow0,
\qquad
d_H(E_n,M)\longrightarrow0.
\tag{3.6}
\]

**Compactness proof.**

\[
\begin{aligned}
d_H(E_n,M)\not\longrightarrow0
&\Longrightarrow
\exists\eta>0\ \exists n_j\uparrow\infty\
\exists x_j\in E_{n_j}:
\operatorname{dist}(x_j,M)\ge\eta,\\
&\Longrightarrow
\exists x\in E_0\ \exists j_\ell\uparrow\infty:
x_{j_\ell}\to x,\\
&\Longrightarrow
x\in\bigcap_nE_n=M
\ \land\ \operatorname{dist}(x,M)\ge\eta,
\end{aligned}
\tag{3.7}
\]

a contradiction. The same argument applies to \(O_n\).

**Logical distinction.**

\[
\begin{aligned}
&\forall k\ \exists n:\ d_H(E_n,M)<2^{-k}
\\[-2pt]
&\hspace{2em}\not\Rightarrow
\text{a specified computable }\nu:\mathbb N\to\mathbb N
\text{ with }d_H(E_{\nu(k)},M)<2^{-k}.
\end{aligned}
\tag{3.8}
\]

## 4. Certified inner stages

### 4.1 Exclusion of the existing bounded-orbit witness stages

**Existing definition.**

\[
J_N=\{c:\forall n,\ |p_n(c)|\le N\}
=\texttt{innerOrbitSet}(N).
\tag{4.1}
\]

**D.**

\[
N\ge2\Longrightarrow J_N=M.
\tag{4.2}
\]

**Proof.**

\[
c\in J_N\Longrightarrow\sup_n|p_n(c)|\le N<\infty,
\qquad
c\in M\Longrightarrow\forall n,\ |p_n(c)|\le2\le N.
\tag{4.3}
\]

\[
\boxed{\text{The predicate defining \(J_N\) contains an infinite quantifier.}}
\tag{4.4}
\]

### 4.2 Finite trapping certificates

**Definition.** A certificate \(\tau=(P,U)\) consists of:

\[
\begin{gathered}
P=[a,b]+i[d,e],\qquad a,b,d,e\in\mathbb Q,\quad a<b,\ d<e,\\
U=\bigcup_{\ell=1}^m
([a_\ell,b_\ell]+i[d_\ell,e_\ell]),
\qquad m\ge1,
\\
a_\ell,b_\ell,d_\ell,e_\ell\in\mathbb Q,\qquad
a_\ell<b_\ell,\ d_\ell<e_\ell.
\end{gathered}
\tag{4.5}
\]

\[
\operatorname{Trap}(P,U)
\iff
0\in\operatorname{int}U
\ \land\
\forall c\in P\ \forall z\in U,\quad z^2+c\in\operatorname{int}U.
\tag{4.6}
\]

\[
\operatorname{Trap}(P,U)
\text{ is a closed first-order formula over }\mathbb Q.
\tag{4.7}
\]

**D. Soundness.**

\[
\operatorname{Trap}(P,U)\Longrightarrow P\subseteq\operatorname{int}M.
\tag{4.8}
\]

**Proof.**

\[
0\in U,\quad f_c(U)\subseteq U
\Longrightarrow \forall n,\ p_n(c)\in U
\Longrightarrow c\in M.
\tag{4.9}
\]

Moreover,

\[
\begin{aligned}
\eta
&=\operatorname{dist}\bigl(
\{z^2+c:c\in P,\ z\in U\},
\mathbb C\setminus\operatorname{int}U
\bigr)>0,\\
\operatorname{dist}(c',P)<\eta
&\Longrightarrow f_{c'}(U)\subseteq\operatorname{int}U
\Longrightarrow c'\in M.
\end{aligned}
\tag{4.10}
\]

**Fixed initial certificate.**

\[
P_*=[-1/16,1/16]+i[-1/16,1/16],
\qquad
U_*=[-1/4,1/4]+i[-1/4,1/4].
\tag{4.11}
\]

\[
c\in P_*,\ z\in U_*
\Longrightarrow
|\operatorname{Re}(z^2+c)|\le1/8<1/4,\quad
|\operatorname{Im}(z^2+c)|\le3/16<1/4.
\tag{4.12}
\]

**Enumeration.** Fix a computable surjection
\(\tau:\mathbb N\to\{\text{data of the form (4.5)}\}\).

\[
I_n=P_*\ \cup\
\bigcup_{\substack{j\le n\\\operatorname{Trap}(\tau(j))}}
P_{\tau(j)}.
\tag{4.13}
\]

**D.**

\[
\varnothing\ne I_n\subseteq I_{n+1}\subseteq\operatorname{int}M,
\qquad I_n\text{ compact}.
\tag{4.14}
\]

### 4.3 The missing inner-density theorem

**O-IN.**

\[
\boxed{
\forall c\in M\ \forall k\in\mathbb N\
\exists n\ \exists z\in I_n:\ |c-z|<2^{-k}.
}
\tag{IN}
\]

**D. Equivalent forms.**

\[
\textup{(IN)}
\iff
\overline{\bigcup_nI_n}=M
\iff
d_H(I_n,M)\longrightarrow0.
\tag{4.15}
\]

**Under (IN).**

\[
\boxed{
M_{\mathrm{inner}}(n):=I_n
\subseteq M\subseteq
M_{\mathrm{ext}}(n):=E_n,
\qquad
M=\overline{\bigcup_nI_n}=\bigcap_nE_n.
}
\tag{4.16}
\]

\[
\bigcup_nI_n=M\text{ is not the target: }
\bigcup_nI_n\subseteq\operatorname{int}M.
\tag{4.17}
\]

**Finite stopping predicate.**

\[
\operatorname{Gap}(k,n)
\iff E_n\subseteq I_n^{+2^{-k}}.
\tag{4.18}
\]

\[
\operatorname{Gap}(k,n)
\Longrightarrow
d_H(E_n,M)\le2^{-k},\quad
d_H(I_n,M)\le2^{-k}.
\tag{4.19}
\]

\[
\textup{(IN)}
\Longrightarrow
\forall k\ \exists n:\operatorname{Gap}(k,n).
\tag{4.20}
\]

\[
\operatorname{Gap}(k,n)\text{ decidable by (2.5)},\qquad
\nu(k)=\min\{n:\operatorname{Gap}(k,n)\}.
\tag{4.21}
\]

**Termination obligation:** (IN). **Local-connectedness implication:** not
established by this construction.

**Optional sufficient density input.**

\[
\mathcal H_0=
\left\{c:
\begin{array}{l}
\exists p\ge1\ \exists z_0,\ldots,z_{p-1}:\
f_c(z_j)=z_{j+1\bmod p},\\
\left|\prod_{j=0}^{p-1}2z_j\right|<1,\qquad
\operatorname{dist}(p_n(c),\{z_0,\ldots,z_{p-1}\})\to0
\end{array}
\right\}.
\tag{4.22}
\]

**D. Trapping-region construction.**

For an attracting cycle \(z_j\), choose \(a_j>|2z_j|\), \(a_j>0\), with
\(\prod_j a_j<1\), and positive radii \(\rho_j\) satisfying

\[
(|2z_j|+\rho_j)\rho_j<\rho_{j+1\bmod p}.
\tag{4.23a}
\]

\[
W_{\mathrm{cyc}}=\bigcup_j\overline B(z_j,\rho_j)
\Longrightarrow
f_c(W_{\mathrm{cyc}})\subseteq\operatorname{int}W_{\mathrm{cyc}}.
\tag{4.23b}
\]

Choose \(N\ge1\) with \(p_N(c)\in\operatorname{int}W_{\mathrm{cyc}}\).
By backward finite induction, choose positive-radius closed balls \(B_m\) about
\(p_m(c)\), \(0\le m<N\), such that

\[
f_c(B_{N-1})\subseteq\operatorname{int}W_{\mathrm{cyc}},
\qquad
f_c(B_m)\subseteq\operatorname{int}B_{m+1}\quad(m<N-1).
\tag{4.23c}
\]

\[
W=W_{\mathrm{cyc}}\cup\bigcup_{m<N}B_m,\qquad
0\in\operatorname{int}W,\qquad
f_c(W)\subseteq\operatorname{int}W.
\tag{4.23d}
\]

Finite rational rectangle covers give \(U\) with

\[
\{0\}\cup f_c(W)\subseteq\operatorname{int}U
\subseteq U\subseteq\operatorname{int}W
\Longrightarrow f_c(U)\subseteq\operatorname{int}U.
\tag{4.23e}
\]

\[
\begin{gathered}
c\in\mathcal H_0
\Longrightarrow
\exists(P,U):\
c\in\operatorname{int}P\ \land\ \operatorname{Trap}(P,U).
\end{gathered}
\tag{4.23}
\]

In the final implication, compact containment permits finite rational
rectangular approximations and a uniform parameter perturbation.

\[
\mathcal H_0\subseteq\bigcup_n I_n,\qquad
\overline{\mathcal H_0}=M\Longrightarrow\textup{(IN)}.
\tag{4.24}
\]

**O-HYP.** \(\overline{\mathcal H_0}=M\); not assumed and not needed for
the outer-limit or address-space theorems.

## 5. Exhaustive classification

### 5.1 Exterior certificates

\[
\mathcal E_m=
\{c:|p_m(c)|>2\ \land\
\forall j<m,\ |p_j(c)|\le2\},
\qquad m\ge1.
\tag{5.1}
\]

\[
\mathbb C\setminus M=\bigsqcup_{m\ge1}\mathcal E_m.
\tag{5.2}
\]

### 5.2 All parameters in \(M\): infinite finite-alphabet addresses

**Definitions.**

\[
\begin{aligned}
\operatorname{par}_n:
V_{n+1}&\longrightarrow V_n,
&
Q_{n+1,a,b}&\longmapsto
Q_{n,\lfloor a/2\rfloor,\lfloor b/2\rfloor},
\\
\mathcal A
&=\left\{
(Q_n)_{n\ge0}\in\prod_nV_n:
\operatorname{par}_n(Q_{n+1})=Q_n
\right\}.
\end{aligned}
\tag{5.3}
\]

**D. Coding theorem.**

\[
\forall\alpha=(Q_n)\in\mathcal A,\
\exists!c\in M:\ \bigcap_nQ_n=\{c\},
\qquad
\pi(\alpha):=c.
\tag{5.4}
\]

\[
\pi:\mathcal A\twoheadrightarrow M,\qquad
\alpha_n=\beta_n\Longrightarrow
|\pi(\alpha)-\pi(\beta)|\le\sqrt2\,2^{-n}.
\tag{5.5}
\]

**Surjectivity proof.**

\[
c\in M
\Longrightarrow
\text{choose recursively a dyadic child containing \(c\)}
\Longrightarrow
\exists(Q_n)\in\mathcal A:\forall n,\ c\in Q_n.
\tag{5.6}
\]

**Exact identification of duplicated addresses.**

\[
\alpha\sim\beta
\iff
\forall n,\ Q_n^\alpha\cap Q_n^\beta\ne\varnothing
\iff
\pi(\alpha)=\pi(\beta).
\tag{5.7}
\]

\[
\mathcal A\text{ compact},\quad
\pi\text{ continuous},\quad
\boxed{\mathcal A/{\sim}\ \cong_{\mathrm{Top}}\ M}.
\tag{5.8}
\]

**Classification scope.**

\[
\begin{aligned}
&\text{Every element of \(M\): an infinite address modulo (5.7).}\\
&\text{Every exterior element: a unique least escape time (5.1).}\\
&\text{Finite survival: not a certificate of infinite survival.}\\
&\text{Address existence: not finite-time membership decidability.}
\end{aligned}
\tag{5.9}
\]

### 5.3 Dynamical refinement: no omitted residual class

For \(c\in M\), let \(\operatorname{Per}(c,p,z)\) mean

\[
p\ge1,\quad f_c^p(z)=z,\quad
\forall q\ (1\le q<p\Longrightarrow f_c^q(z)\ne z),
\qquad
\lambda(c,p,z)=(f_c^p)'(z).
\tag{5.10}
\]

Define predicates:

| Predicate | Exact condition |
| --- | --- |
| \(A(c)\) | \(\exists p,z:\operatorname{Per}(c,p,z)\land|\lambda(c,p,z)|<1\) |
| \(P(c)\) | \(\exists p,z,q\ge1:\operatorname{Per}(c,p,z)\land\lambda(c,p,z)^q=1\) |
| \(S(c)\) | An irrationally indifferent periodic germ analytically conjugate to its linear part |
| \(C(c)\) | An irrationally indifferent periodic germ not analytically conjugate to its linear part |
| \(F(c)\) | \(\exists a\ge0,\ b\ge1:\ p_{a+b}(c)=p_a(c)\) |

Here, for \(\operatorname{Per}(c,p,z)\),

\[
\begin{aligned}
\operatorname{IrrNeutral}(c,p,z)
&\iff |\lambda(c,p,z)|=1\
\land\ \forall q\ge1,\ \lambda(c,p,z)^q\ne1,\\
\operatorname{Linearizable}(c,p,z)
&\iff
\exists\text{ biholomorphic germ }\psi\text{ at }0:\\
&\hspace{2em}\psi(0)=z,\quad
f_c^p(\psi(w))=\psi(\lambda(c,p,z)w)
\text{ as germs}.
\end{aligned}
\tag{5.11}
\]

\[
\begin{aligned}
S(c)&\iff\exists p,z:
\operatorname{Per}(c,p,z)\land
\operatorname{IrrNeutral}(c,p,z)\land
\operatorname{Linearizable}(c,p,z),\\
C(c)&\iff\exists p,z:
\operatorname{Per}(c,p,z)\land
\operatorname{IrrNeutral}(c,p,z)\land
\neg\operatorname{Linearizable}(c,p,z).
\end{aligned}
\tag{5.12}
\]

**Disjoint convention.** Put \(B_0=A,B_1=P,B_2=S,B_3=C,B_4=F\), and

\[
D_j=\{c\in M:B_j(c)\land\forall i<j,\neg B_i(c)\},
\quad 0\le j\le4,
\qquad
D_5=\{c\in M:\forall i\le4,\neg B_i(c)\}.
\tag{5.13}
\]

\[
M=\bigsqcup_{j=0}^5D_j,
\qquad
\mathcal A_j=\pi^{-1}(D_j),
\qquad
\pi(\mathcal A_j)=D_j.
\tag{5.14}
\]

**O-CLASS.** A proof strategy using this partition must establish its
required component estimates on every \(D_j\), including \(D_5\).

\[
\forall j\in\{0,\ldots,5\}\ \forall c\in D_j\
\forall\varepsilon>0\
\exists\,0<\delta<r<\varepsilon\
\forall N\ \exists L\ge N:\quad
O_L\cap\overline B(c,\delta)
\subseteq\operatorname{Comp}(O_N\cap\overline B(c,r),c).
\tag{5.15a}
\]

\[
\begin{gathered}
D_5\text{ is retained, not declared empty};\\
\text{a partition by predicates}
\ne
\text{a finite algorithm deciding those predicates};\\
\text{equality of proposed dynamical invariants}
\Longrightarrow c=c'
\quad\text{requires a separate rigidity theorem}.
\end{gathered}
\tag{5.15}
\]

## 6. The finite-component theorem required by the root

### 6.1 Existing root predicate

\[
C_N(c,r)=\operatorname{Comp}(O_N\cap\overline B(c,r),c),
\qquad c\in M.
\tag{6.1}
\]

\[
\begin{aligned}
\mathrm{BUF}\iff
\forall c\in M\ \forall\varepsilon>0\
\exists r,\delta:\;&0<\delta<r<\varepsilon\\
&{}\land
\forall N\ \exists L\ge N:\
O_L\cap\overline B(c,\delta)\subseteq C_N(c,r).
\end{aligned}
\tag{BUF}
\]

**R.**

\[
\mathrm{BUF}
=\texttt{MandelbrotUniformOuterBuffer},
\qquad
\mathrm{BUF}\Longrightarrow
\texttt{MLC.RootInput}\Longrightarrow
\operatorname{LocallyConnected}(M).
\tag{6.2}
\]

### 6.2 Finite semialgebraic component certificates

**T.** A compact semialgebraic set has finitely many connected components;
each component is compact and semialgebraic.

**O-COMP.** For every \(N\) and closed rational rectangle \(R\), construct
a finite family

\[
\mathscr C(N,R)=\{K_1,\ldots,K_s\},
\tag{6.3}
\]

with certificates for

\[
\begin{gathered}
O_N\cap R=\bigsqcup_{\ell=1}^sK_\ell,\qquad
K_\ell\ne\varnothing,\qquad
K_\ell\text{ compact and connected},\\
\mathscr C(N,R)=\pi_0(O_N\cap R).
\end{gathered}
\tag{6.4}
\]

**Finite realization options.**

\[
\begin{aligned}
&\text{certified semialgebraic component decomposition};\\
&\text{certified finite triangulation}
\ \longrightarrow\
\text{connected components of its incidence graph}.
\end{aligned}
\tag{6.5}
\]

\[
\text{Algebraic coefficient encoding}
=(\text{integer polynomial},\ \text{rational isolating interval}).
\tag{6.5a}
\]

\[
\text{Certificate obligations}
=\text{root isolation}+\text{sign correctness}
+\text{coverage}+\text{component correctness}.
\tag{6.5b}
\]

\[
\text{Overlapping numerical enclosures}
\not\Longrightarrow
\text{intersection of the enclosed sets}.
\tag{6.6}
\]

### 6.3 A fully quantified finite-cover criterion

For closed rational rectangles \(P\subseteq\operatorname{int}R\), define

\[
\operatorname{Cert}(P,R,N,L)
\iff
L\ge N\
\land\
\exists K\in\mathscr C(N,R):\
O_L\cap P\subseteq K.
\tag{6.7}
\]

**O-FC.**

\[
\boxed{
\begin{aligned}
\forall k\in\mathbb N\
\exists m\ge1\
\exists(P_i,R_i)_{i=1}^m\
\exists T\in\mathbb N:\quad&
\\
\forall i,\quad
P_i\subseteq\operatorname{int}R_i,\quad
\operatorname{diam}R_i<2^{-k},\qquad&
\\
O_T\subseteq\bigcup_{i=1}^m\operatorname{int}P_i,\qquad&
\\
\forall N\in\mathbb N\
\exists L\ge N\
\forall i,\quad
\operatorname{Cert}(P_i,R_i,N,L).&
\end{aligned}
}
\tag{FC}
\]

**Finite data at fixed \(k,N\).**

\[
(m,(P_i,R_i)_i,T,L,(\mathscr C(N,R_i))_i,
\text{coverage and inclusion certificates}).
\tag{6.8}
\]

**Quantifier constraint.**

\[
\exists(P_i,R_i,T)\ \forall N\ \exists L
\quad\ne\quad
\forall N\ \exists(P_i,R_i,T,L).
\tag{6.9}
\]

### 6.4 Proof that (FC) implies local connectedness

Fix \(c\in M\) and choose \(i\) with \(c\in\operatorname{int}P_i\).

\[
K_N=\operatorname{Comp}(O_N\cap R_i,c).
\tag{6.10}
\]

\[
\begin{aligned}
\operatorname{Cert}(P_i,R_i,N,L),\ c\in O_L\cap P_i
&\Longrightarrow M\cap P_i\subseteq K_N,\\
K_{N+1}&\subseteq K_N,\\
K_\infty:=\bigcap_NK_N
&\text{ is nonempty, compact, and connected},\\
M\cap P_i\subseteq K_\infty
&\subseteq M\cap R_i.
\end{aligned}
\tag{6.11}
\]

\[
c\in\operatorname{int}P_i,\quad
\operatorname{diam}R_i<2^{-k}
\Longrightarrow
K_\infty\text{ is a connected neighborhood of \(c\) in \(M\)}
\text{ of diameter }<2^{-k}.
\tag{6.12}
\]

\[
\boxed{\textup{(FC)}\Longrightarrow\operatorname{LocallyConnected}(M).}
\tag{6.13}
\]

### 6.5 Reverse reduction for the semialgebraic orbit stages

**D, using T from 6.2.**

\[
\operatorname{LocallyConnected}(M)\Longrightarrow\mathrm{BUF}.
\tag{6.14}
\]

**Proof.** Given \(c\in M\) and \(\varepsilon>0\), choose a connected
relative neighborhood \(V\) of \(c\) and \(r,\delta\) such that

\[
0<\delta<r<\varepsilon,\qquad
M\cap\overline B(c,\delta)\subseteq V
\subseteq M\cap B(c,r).
\tag{6.15}
\]

For fixed \(N\), \(F_N=O_N\cap\overline B(c,r)\) is compact semialgebraic
(real coefficients are allowed), hence

\[
F_N\setminus C_N(c,r)
\text{ is a finite union of compact components}.
\tag{6.16}
\]

Put

\[
B_N=
\bigl(F_N\setminus C_N(c,r)\bigr)\cap\overline B(c,\delta).
\tag{6.17}
\]

\[
B_N\text{ compact},\qquad
B_N\cap M=\varnothing,\qquad
\bigcap_{L\ge N}(B_N\cap O_L)=\varnothing.
\tag{6.18}
\]

Compactness and nesting imply

\[
\exists L\ge N:\ B_N\cap O_L=\varnothing
\Longrightarrow
O_L\cap\overline B(c,\delta)\subseteq C_N(c,r).
\tag{6.19}
\]

**D.** The same argument with rational rectangles gives

\[
\operatorname{LocallyConnected}(M)\Longrightarrow\textup{(FC)}.
\tag{6.20}
\]

**Finite-cover construction.**

\[
\begin{gathered}
\forall c\in M,\ \exists P_c,R_c,V_c:\quad
c\in\operatorname{int}P_c,\quad
P_c\subseteq\operatorname{int}R_c,\quad
\operatorname{diam}R_c<2^{-k},\\
M\cap P_c\subseteq V_c\subseteq M\cap R_c,\qquad
V_c\text{ connected}.
\end{gathered}
\tag{6.21}
\]

\[
\begin{aligned}
M\text{ compact}
&\Longrightarrow
M\subseteq\bigcup_{i=1}^m\operatorname{int}P_{c_i},\\
O_N\downarrow M
&\Longrightarrow
\exists T:\ O_T\subseteq\bigcup_{i=1}^m\operatorname{int}P_{c_i},\\
\text{(6.16)--(6.19), for each \(i\)}
&\Longrightarrow
\forall N\ \exists L_1,\ldots,L_m,\\
L=\max(N,L_1,\ldots,L_m)
&\Longrightarrow
\forall i,\ \operatorname{Cert}(P_{c_i},R_{c_i},N,L).
\end{aligned}
\tag{6.22}
\]

**Exact frontier.**

\[
\boxed{
\textup{(FC)}
\iff\mathrm{BUF}
\iff\operatorname{LocallyConnected}(M).
}
\tag{6.23}
\]

\[
\boxed{
\text{Finite decision of each certificate}
\ne
\text{proof of the universally quantified criterion (FC)}.
}
\tag{6.24}
\]

## 7. Deformation through coherent parametrizations

Let \(\mathbb D=\overline B(0,1)\subseteq\mathbb C\).

**O-PARAM.** Construct continuous maps \(h_n:\mathbb D\to\mathbb C\)
and nonnegative real numbers \(a_n\) satisfying

\[
\sum_na_n<\infty,\qquad
\sup_{u\in\mathbb D}|h_{n+1}(u)-h_n(u)|\le a_n,
\qquad
d_H(h_n(\mathbb D),M)\longrightarrow0.
\tag{7.1}
\]

**D.**

\[
\exists h\in C(\mathbb D,\mathbb C):
\|h-h_n\|_\infty\le\sum_{j\ge n}a_j,
\qquad
h(\mathbb D)=M.
\tag{7.2}
\]

**Proof.**

\[
\begin{aligned}
\|h_m-h_n\|_\infty
&\le\sum_{j=n}^{m-1}a_j,\\
d_H(h_n(\mathbb D),h(\mathbb D))
&\le\|h_n-h\|_\infty\longrightarrow0,\\
d_H(h(\mathbb D),M)&=0.
\end{aligned}
\tag{7.3}
\]

**T. Hahn--Mazurkiewicz implication.**

\[
\mathbb D\twoheadrightarrow M
\text{ continuously}
\Longrightarrow
M\text{ compact, connected, and locally connected}.
\tag{7.4}
\]

**Permitted specializations of O-PARAM.**

| Route | Additional data |
| --- | --- |
| Outer | \(h_n(\mathbb D)=A_n\), where \(A_n\supseteq M\) and \(d_H(A_n,M)\to0\) |
| Inner | \(h_n(\mathbb D)=J_n\subseteq M\) and \(d_H(J_n,M)\to0\) |
| Two-sided | Both sequences, with separately certified image inclusions and uniform convergence |

\[
I_n\text{ need not be connected}
\Longrightarrow
\text{a surjection }\mathbb D\twoheadrightarrow I_n
\text{ is not presumed}.
\tag{7.5}
\]

\[
h_n\text{ individually continuous}
\ \land\
d_H(h_n(\mathbb D),M)\to0
\quad\not\Rightarrow\quad
\text{(7.1)}.
\tag{7.6}
\]

## 8. External-potential flow

### 8.1 Classical analytic input

**T. Mandelbrot exterior uniformization.**

\[
\begin{gathered}
\Omega=\widehat{\mathbb C}\setminus M,\qquad
\Phi:\Omega\xrightarrow{\ \cong_{\mathrm{conf}}\ }
\{w\in\widehat{\mathbb C}:|w|>1\},\\
\Phi(\infty)=\infty,\qquad
\lim_{z\to\infty}\Phi(z)/z=1,\qquad
\Psi=\Phi^{-1}.
\end{gathered}
\tag{8.1}
\]

For finite \(z\notin M\), put \(g(z)=\log|\Phi(z)|\), and set \(g=0\)
on \(M\).

\[
g\in C(\mathbb C,[0,\infty)),\qquad
g^{-1}(0)=M.
\tag{8.2}
\]

**T. Normalization.**

\[
G_c(z)=\lim_{n\to\infty}2^{-n}\log\max(1,|f_c^n(z)|),
\qquad
g(c)=G_c(c)=2G_c(0).
\tag{8.2a}
\]

**Definitions, \(s>0\).**

\[
A_s=\{z:g(z)\le s\},
\qquad
\Gamma_s=\{\Psi(e^{s+i\theta}):\theta\in\mathbb R/2\pi\mathbb Z\}.
\tag{8.3}
\]

**T. Jordan--Schoenflies consequences.**

\[
A_s\cong_{\mathrm{Top}}\mathbb D,\qquad
0<t<s\Longrightarrow M\subseteq A_t\subseteq\operatorname{int}A_s,\qquad
\bigcap_{s>0}A_s=M.
\tag{8.4}
\]

\[
\text{Analytic existence of \(A_s\)}
\ne
\text{finite rational certificate for \(A_s\)}.
\tag{8.5}
\]

### 8.2 Exterior flow equation

For \(t\ge0\), \(z\in\mathbb C\setminus M\), define

\[
F_t(z)=
\Psi\left(
\exp(e^{-t}g(z))\,\frac{\Phi(z)}{|\Phi(z)|}
\right).
\tag{8.6}
\]

**D.**

\[
\begin{aligned}
F_0(z)&=z,\\
F_{t+u}(z)&=F_t(F_u(z)),\\
g(F_t(z))&=e^{-t}g(z),\\
F_t(A_s\setminus M)&=A_{e^{-t}s}\setminus M,\\
\partial_tF_t(z)&=
-g(F_t(z))\,
\frac{\Phi(F_t(z))}{\Phi'(F_t(z))}.
\end{aligned}
\tag{8.7}
\]

**Terminal-time distinction.**

\[
g(F_t(z))\to0
\quad\not\Rightarrow\quad
\text{existence and joint continuity of }
\lim_{t\to\infty}F_t(z).
\tag{8.8}
\]

### 8.3 Exact terminal-extension obligation

**O-EXT.** For one \(s>0\), construct a continuous extension

\[
\overline\Psi:
\{w:1\le|w|\le e^s\}\longrightarrow A_s,
\qquad
\overline\Psi|_{\{1<|w|\le e^s\}}=\Psi.
\tag{EXT}
\]

**D, under (EXT).**

\[
\overline\Psi(S^1)=\partial M.
\tag{8.9}
\]

Define \(H:A_s\times[0,1]\to A_s\) by

\[
H(z,u)=
\begin{cases}
z,&z\in M,\\
\overline\Psi\left(
\exp((1-u)g(z))\dfrac{\Phi(z)}{|\Phi(z)|}
\right),&z\notin M.
\end{cases}
\tag{8.10}
\]

\[
H(z,0)=z,\qquad
H(c,u)=c\ (c\in M),\qquad
H(A_s,1)=M.
\tag{8.11}
\]

**Continuity at the gluing locus.**

\[
\begin{gathered}
z_j\notin M,\ z_j\to c\in M
\Longrightarrow g(z_j)\to0,\\
w_j=\Phi(z_j),\quad
\widetilde w_j=
\exp((1-u_j)g(z_j))\,w_j/|w_j|,\\
|\widetilde w_j-w_j|
\le e^{g(z_j)}-1\longrightarrow0,\\
\overline\Psi\text{ uniformly continuous}
\Longrightarrow
H(z_j,u_j)-z_j\longrightarrow0.
\end{gathered}
\tag{8.12}
\]

**Consequences.**

\[
\boxed{
\textup{(EXT)}
\Longrightarrow
M\text{ is a strong deformation retract of }A_s
\Longrightarrow
\operatorname{LocallyConnected}(M).
}
\tag{8.13}
\]

\[
A_s\cong\mathbb D,\quad H(\,\cdot\,,1):A_s\twoheadrightarrow M
\quad\stackrel{(7.4)}{\Longrightarrow}\quad
\operatorname{LocallyConnected}(M).
\tag{8.14}
\]

**T. Caratheodory criterion for a full planar continuum.**

\[
\boxed{
\operatorname{LocallyConnected}(M)
\iff
\operatorname{LocallyConnected}(\partial M)
\iff
\textup{(EXT)}.
}
\tag{8.14a}
\]

\[
\overline\Psi|_{S^1}\text{ is a continuous surjection};
\qquad
\text{injectivity is not required}.
\tag{8.14b}
\]

**No circular use.**

\[
\text{A boundary-extension theorem requiring local connectedness}
\not\Longrightarrow
\text{an independent proof of (EXT)}.
\tag{8.15}
\]

### 8.4 Uniform radial oscillation

For \(0<a\le s\), define

\[
\omega(a)=
\sup_{\theta\in\mathbb R/2\pi\mathbb Z}\
\sup_{0<u,v\le a}
|\Psi(e^{u+i\theta})-\Psi(e^{v+i\theta})|.
\tag{8.16}
\]

**O-RAD.**

\[
\boxed{
\forall k\in\mathbb N\
\exists a\in\mathbb Q:\quad
0<a\le\min(s,2^{-k})\ \land\ \omega(a)\le2^{-k}.
}
\tag{RAD}
\]

**D.**

\[
\textup{(RAD)}
\iff
\lim_{a\downarrow0}\omega(a)=0
\iff
\textup{(EXT)}.
\tag{8.17}
\]

**Proof.** Put \(\psi_u(\theta)=\Psi(e^{u+i\theta})\). Then

\[
\begin{aligned}
\omega(a)\to0
&\Longrightarrow
(\psi_u)_{u\downarrow0}\text{ uniformly Cauchy},\\
&\Longrightarrow
\exists\lambda\in C(S^1,\mathbb C):
\|\psi_u-\lambda\|_\infty\to0,\\
\overline\Psi(e^{u+i\theta})
&=
\begin{cases}
\psi_u(\theta),&u>0,\\
\lambda(\theta),&u=0
\end{cases}
\quad\text{is continuous}.
\end{aligned}
\tag{8.18}
\]

Conversely, uniform continuity of \(\overline\Psi\), together with
\[
0<u,v\le a
\Longrightarrow
|e^{u+i\theta}-e^{v+i\theta}|\le e^a-1,
\tag{8.19}
\]
implies \(\omega(a)\to0\).

\[
\boxed{
\textup{(RAD)}
\iff\textup{(EXT)}
\iff\mathrm{BUF}
\iff\operatorname{LocallyConnected}(M).
}
\tag{8.20}
\]

## 9. Homotopy equivalence to a disk

**D. For nonempty \(X\).**

\[
X\simeq\mathbb D
\iff
X\simeq\{*\}
\iff
X\text{ is contractible}.
\tag{9.1}
\]

**Counterexample to sufficiency for local connectedness.**

\[
K=
([0,1]\times\{0\})
\cup(\{0\}\times[0,1])
\cup\bigcup_{n\ge1}(\{1/n\}\times[0,1]).
\tag{9.2}
\]

\[
H_K((x,y),u)=
\begin{cases}
(x,(1-2u)y),&0\le u\le1/2,\\
((2-2u)x,0),&1/2\le u\le1.
\end{cases}
\tag{9.3}
\]

\[
H_K:K\times[0,1]\to K
\text{ continuous},\qquad
H_K(-,0)=\operatorname{id},\quad
H_K(-,1)=(0,0).
\tag{9.4}
\]

For \(0<a<b<1\),

\[
K\cap\{a<y<b\}
\text{ has components }
\{x\}\times(a,b),\quad
x\in\{0\}\cup\{1/n:n\ge1\}.
\tag{9.5}
\]

\[
\{0\}\times(a,b)\text{ is not relatively open}
\Longrightarrow
K\text{ is not locally connected}.
\tag{9.6}
\]

\[
\boxed{
M\simeq\mathbb D
\text{ alone is not a sufficient root input.}
}
\tag{9.7}
\]

**Distinct obligations.**

| Statement | Strength relevant to the root |
| --- | --- |
| \(A_n\cong\mathbb D,\ A_n\downarrow M\) | Disk approximation; no terminal map |
| \(M\simeq\mathbb D\) | Contractibility; no local-connectedness conclusion |
| Continuous surjection \(\mathbb D\twoheadrightarrow M\) | Sufficient for local connectedness |
| Retraction \(r:A_s\to M\) | Sufficient for local connectedness |
| Strong deformation retraction \(A_s\searrow M\) | Also implies contractibility |

### 9.1 Cellularity and shape

**T.**

\[
A_{2^{-(n+1)}}\subseteq\operatorname{int}A_{2^{-n}},
\qquad A_{2^{-n}}\cong\mathbb D,
\qquad \bigcap_nA_{2^{-n}}=M
\Longrightarrow
M\text{ is cellular in }\mathbb R^2.
\tag{9.8}
\]

\[
M\text{ cellular}
\Longrightarrow
M\text{ cell-like}
\Longrightarrow
\operatorname{Shape}(M)=\operatorname{Shape}(\{*\}).
\tag{9.9}
\]

\[
\operatorname{Shape}(X)=\operatorname{Shape}(\{*\})
\quad\text{and}\quad
X\simeq\{*\}
\quad\text{are distinct conditions for compact metric spaces}.
\tag{9.10}
\]

### 9.2 The ambient-disk retraction criterion

**Definitions, in the category of metric spaces.**

\[
\begin{aligned}
X\in\mathrm{AR}
&\iff
\text{every closed embedding }i:X\hookrightarrow Y
\text{ admits a retraction }Y\to i(X),\\
X\in\mathrm{ANR}
&\iff
\text{every such embedding admits a retraction }
U\to i(X)\\
&\hspace{2em}
\text{for some open }U\subseteq Y\text{ containing }i(X).
\end{aligned}
\tag{9.11}
\]

Let \(B=\overline B(0,R)\), \(R>2\).

**T. Borsuk's planar AR theorem, applied to the full continuum \(M\).**

\[
\boxed{
\operatorname{LocallyConnected}(M)
\iff M\in\mathrm{AR}
\iff M\in\mathrm{ANR}
\iff \exists r:B\to M\text{ continuous},\ r|_M=\operatorname{id}
\iff B\searrow M.
}
\tag{9.12}
\]

**Retraction-to-deformation formula.**

\[
H_B(x,u)=(1-u)x+u\,r(x)\in B,\qquad
H_B(c,u)=c\quad(c\in M).
\tag{9.13}
\]

**Contraction formula, for fixed \(c_0\in M\).**

\[
K_M(c,u)=r((1-u)c+u c_0)\in M,\qquad
K_M(c,0)=c,\quad K_M(c,1)=c_0.
\tag{9.14}
\]

\[
\operatorname{LocallyConnected}(M)\Longrightarrow M\simeq\mathbb D;
\qquad
\text{the converse is not used}.
\tag{9.15}
\]

## 10. Ricci-flow formulation: additional structures required

**Data.**

\[
\begin{gathered}
\Sigma:\text{fixed compact smooth surface with boundary},\\
\gamma_t:\text{Riemannian metrics on }\Sigma,\qquad
e_t:\Sigma\to\mathbb C.
\end{gathered}
\tag{10.1}
\]

**Intrinsic equation.**

\[
\partial_t\gamma_t=-2K_{\gamma_t}\gamma_t
\quad\text{on }\operatorname{int}\Sigma.
\tag{10.2}
\]

**O-RF. Required additional data and proofs.**

\[
\begin{gathered}
\text{initial metric and specified boundary conditions};\\
\text{existence, uniqueness, and required lifetime};\\
\text{an evolution law for }e_t
\text{ and a proved coupling to }\gamma_t;\\
e_t(\Sigma)=A_{\sigma(t)}
\text{ or certified inner images in }M;\\
\text{uniform convergence }e_t\to e_\infty;\\
e_\infty(\Sigma)=M.
\end{gathered}
\tag{10.3}
\]

\[
\text{Equation (10.2) alone}
\not\Longrightarrow
\text{any equation or limit for }e_t(\Sigma)\subseteq\mathbb C.
\tag{10.4}
\]

\[
\text{Preferred specified flow: (8.6)--(8.7)};
\qquad
\text{its unresolved terminal obligation: (EXT)}.
\tag{10.5}
\]

## 11. Lean implementation order and theorem interfaces

| Order | Proposed module | Required result | Status |
| --- | --- | --- | --- |
| 1 | `Mlc/CertifiedOrbitApproximation.lean` | (2.3)--(3.7); (4.2) | D; O-QE for executable cell selection |
| 2 | `Mlc/CertifiedTrappingRegions.lean` | (4.8), (4.12)--(4.14); checker soundness | D; O-QE or specialized interval certificates |
| 3 | `Mlc/ParameterAddressSpace.lean` | (5.4)--(5.8) | D; no MLC hypothesis |
| 4 | `Mlc/SemialgebraicComponentCertificates.lean` | (6.4), decidable (6.7) | O-COMP |
| 5 | `Mlc/FiniteComponentCriterion.lean` | (6.13), (6.14), (6.23) | D, using finite-component theorems |
| 6 | Dynamical estimates for all classes (5.13) | (FC), with its displayed quantifier order | O-FC; principal root obligation |
| 7a | Inner-density development | (IN), totality of (4.21) | O-IN; independent of step 6 |
| 7b | Coherent parametrizations | (7.1) | O-PARAM; alternative root route |
| 7c | External-flow development | (8.1)--(8.7), then (RAD), equivalently (EXT) | T, D, then O-RAD |

**Root assembly after step 6.**

```lean
def rootInputOfBuffer
    (h : MLC.ParameterComponent.MandelbrotUniformOuterBuffer) :
    MLC.RootInput :=
  ⟨h⟩
```

\[
\begin{aligned}
&\texttt{finiteCoverCriterion\_implies\_uniformOuterBuffer}:
  \mathrm{FC}\to\mathrm{BUF},
\\
&\texttt{proveFiniteCoverCriterion}:\mathrm{FC}
\quad\textbf{[O-FC; not declared as an axiom]},
\\
&\texttt{MLC.mlc\_conjecture}\,
  \langle
  \texttt{finiteCoverCriterion\_implies\_uniformOuterBuffer}\,
  \texttt{proveFiniteCoverCriterion}
  \rangle.
\end{aligned}
\tag{11.1}
\]

**Unproved implications; none asserted for \(M\).**

\[
\begin{gathered}
\text{(IN)}\ \Longrightarrow\ \text{(FC)},\\
\text{(3.3) and (5.8)}\ \Longrightarrow\ \text{(FC)},\\
\text{contractibility of \(M\)}\ \Longrightarrow\ \text{(FC)},\\
\text{finite-time exterior flow}\ \Longrightarrow\ \text{(EXT)}.
\end{gathered}
\tag{11.2}
\]

**Excluded model substitution.**

\[
\text{the frozen translated Green tower}
\ne\text{a shrinking parameter-puzzle system}.
\tag{11.3}
\]

## 12. Sources and existing declarations

| Item | Source |
| --- | --- |
| \(O_N\), compactness, nesting, exact intersection | [`Mlc/CategoricalMandelbrot.lean`](../Mlc/CategoricalMandelbrot.lean) |
| BUF; compact component intersections; BUF implies local connectedness | [`Mlc/ParameterComponentApproximation.lean`](../Mlc/ParameterComponentApproximation.lean) |
| Explicit root input | [`Mlc/CategoricalRoot.lean`](../Mlc/CategoricalRoot.lean) |
| Verified integer interval arithmetic | [`Mlc/GreenSublevelIntersectionCounterexample.lean`](../Mlc/GreenSublevelIntersectionCounterexample.lean) |
| Frozen-model exclusions | [`Mlc/ModelRegression.lean`](../Mlc/ModelRegression.lean) |
| Real quantifier elimination and CAD | [M. England, arXiv:2407.19781](https://arxiv.org/abs/2407.19781) |
| Semialgebraic components and triangulation | S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, 2nd ed. |
| Exterior uniformization, normalization | [Douady--Hubbard, *Orsay Notes*, Theorem 8.1 and Corollaries 8.3--8.4, pp. 64--65](https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf#page=64) |
| Boundary extension for full continua | [*Orsay Notes*, Caratheodory corollary and Theorem 2.1, pp. 14--17](https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf#page=14) |
| Planar AR theorem | [Borsuk's theorem, stated in Dudak, TOPOSYM 2022, slide 6](http://www.toposym.cz/slides/slides-Dud_ak-23.pdf#page=6) |
| ANRs, cellularity, shape | [S. Mardesic, *Absolute Neighborhood Retracts and Shape Theory*, pp. 243, 248, 253](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/mardesic.pdf) |
| Effective exterior and hyperbolic enumeration | [P. Hertling, *Computability of the Mandelbrot set*, slides 10--12](https://web.math.wisc.edu/logic/conf/OW21/questions/Hertling.pdf#page=10) |
| Hyperbolicity-density frontier | [A. M. Benini, arXiv:1709.09869, Section 3](https://arxiv.org/html/1709.09869v1#S3) |
| Continuous images of an interval | Hahn--Mazurkiewicz theorem |
