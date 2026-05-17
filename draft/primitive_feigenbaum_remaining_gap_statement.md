# Primitive Feigenbaum remaining mathematical gap

Let
\[
f_c(z)=z^2+c,\qquad c\in\mathbb C,
\]
and assume that \(f_c\) is infinitely renormalizable. Let
\[
g_n:U_n\to V_n,\qquad n\ge 0,
\]
be the successive normalized quadratic-like renormalizations of \(f_c\), where:

1. \(g_{n+1}\) is the first renormalization of \(g_n\);
2. each renormalization is primitive;
3. the renormalization periods \(p_n\) are uniformly bounded:
   \[
   p_n\le P \quad \text{for all } n
   \]
   for some fixed \(P\in \mathbb N\).

For each \(n\), define the fundamental annulus
\[
A_n^{\mathrm{fund}}:=V_n\setminus U_n,
\]
and let \(Q_n\) be the cumulative return time corresponding to the \(n\)-th renormalization level. Let
\[
A_n^{\mathrm{princ}}
\]
denote the corresponding principal-nest annulus in the dynamical plane of \(f_c\), i.e. the annulus between the two principal nest pieces whose first return map, after the standard affine normalization, gives \(g_n\).

The missing mathematical input is the conjunction of the following two theorems.

## Theorem A — Primitive Feigenbaum finite-family positive fundamental modulus

Under the assumptions above, there exist:

- an integer \(N\ge 0\),
- a finite set \(\mathcal F\) of normalized quadratic-like maps,
- a constant \(\mu>0\),

such that for every \(n\ge N\),

1. \(g_n\in \mathcal F\);
2. the fundamental annulus modulus is uniformly positive:
   \[
   \operatorname{mod}(A_n^{\mathrm{fund}})
   =\operatorname{mod}(V_n\setminus U_n)\ge \mu .
   \]

Equivalently:
\[
\exists N\in\mathbb N\ \exists \mu>0\ \exists \mathcal F \text{ finite}\quad
\forall n\ge N,\quad
g_n\in\mathcal F
\ \text{ and }\ 
\operatorname{mod}(V_n\setminus U_n)\ge \mu.
\]

## Theorem B — Principal-nest / renormalized fundamental-annulus comparison

Under the same assumptions, there exists an integer \(N'\ge 0\) such that for every \(n\ge N'\),
\[
\operatorname{mod}\!\left(A_n^{\mathrm{princ}}\right)
=
\operatorname{mod}\!\left(A_n^{\mathrm{fund}}\right)
=
\operatorname{mod}(V_n\setminus U_n).
\]

Equivalently:
\[
\exists N'\in\mathbb N\quad
\forall n\ge N',\quad
\operatorname{mod}(A_n^{\mathrm{princ}})
=
\operatorname{mod}(V_n\setminus U_n).
\]

## Combined corollary needed downstream

From Theorems A and B it follows immediately that there exist \(\mu>0\) and \(N''\) such that for all \(n\ge N''\),
\[
\operatorname{mod}(A_n^{\mathrm{princ}})\ge \mu.
\]

This is the exact remaining mathematical statement needed to discharge the current formal gap.

In single-statement form:
\[
\exists N\in\mathbb N\ \exists \mu>0\ \exists \mathcal F \text{ finite}\quad
\forall n\ge N,\quad
g_n\in\mathcal F,\qquad
\operatorname{mod}(A_n^{\mathrm{princ}})
=
\operatorname{mod}(V_n\setminus U_n)
\ge \mu.
\]
