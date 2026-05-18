# Standalone problem: typewise real bounds for bounded primitive Feigenbaum towers

## Repository target

This note states the remaining theorem-data interface

```lean
PrimitiveFeigenbaumTypewiseRealBoundsGlobalData
```

in standard mathematical notation.

---

## Mathematical setup

Let
\[
f_c(z)=z^2+c,\qquad c\in\mathbb C,
\]
and let
\[
T=(g_n)_{n\ge 0}
\]
be a renormalization tower of quadratic-like maps
\[
g_n:U_n\to V_n.
\]

Assume:

1. every renormalization step \(g_n\rightsquigarrow g_{n+1}\) is primitive;
2. the relative renormalization periods \(p_n\) are uniformly bounded:
   \[
   \exists P\in\mathbb N,\ \forall n\ge 0,\quad p_n\le P.
   \]

For each \(n\), let \(\tau_n\) be the primitive combinatorial type of the step
\[
g_n\rightsquigarrow g_{n+1}.
\]
Let \(\mathcal F_P\) be the finite set of primitive combinatorial types of
period at most \(P\).

For \(n\) sufficiently large, let \(I_{n+1}\subset J_n\subset \mathbb R\) be the
central return interval and ambient interval arising from the real-symmetric
renormalization geometry of \(g_n\). Let \(L_n\) and \(R_n\) be the left and
right complementary gaps of \(I_{n+1}\) inside \(J_n\).

---

## Exact theorem requested

**Problem / Theorem.**  
Prove that there exist:

1. a transient depth \(N_0\in\mathbb N\), and
2. a function
   \[
   C:\mathcal F_P\to \mathbb R_{>0},
   \]

such that for every \(n\ge N_0\),
\[
\frac{|L_n|}{|I_{n+1}|}\ge C(\tau_n),
\qquad
\frac{|R_n|}{|I_{n+1}|}\ge C(\tau_n).
\]

Equivalently: each bounded primitive combinatorial type \(\tau\) carries a
strictly positive real a priori bound \(C(\tau)\), and sufficiently deep levels
of the tower satisfy the corresponding typewise gap-ratio lower bounds.

---

## Quantified form

\[
\forall c,\ \forall T,\ 
\bigl[\text{all renormalizations primitive}\bigr]
\wedge
\bigl[\text{periods uniformly bounded}\bigr]
\Longrightarrow
\exists N_0,\ \exists C:\mathcal F_P\to \mathbb R_{>0},
\]
\[
\forall n\ge N_0,\qquad
\frac{|L_n|}{|I_{n+1}|}\ge C(\tau_n)
\ \text{ and }\
\frac{|R_n|}{|I_{n+1}|}\ge C(\tau_n).
\]

---

## Role in the proof graph

This is the purely real-dynamical input. It is the first half of Step 1 in the
primitive complex-bounds route:

\[
\text{bounded primitive combinatorics}
\Longrightarrow
\text{typewise real gap bounds}
\Longrightarrow
\text{typewise conformal modulus bounds}
\Longrightarrow
\text{uniform eventual lower bound}.
\]
