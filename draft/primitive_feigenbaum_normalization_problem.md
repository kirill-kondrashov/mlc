# Standalone problem: affine normalization comparison for primitive Feigenbaum towers

## Repository target

This note states the remaining theorem-data interface

```lean
PrimitiveFeigenbaumNormalizationGlobalData
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
be a renormalization tower with cumulative depths \(Q_n\).

For each \(n\), let
\[
A_n^{\mathrm{princ}}
:=
P_{Q_n}(c)\setminus P_{Q_{n+1}}(c)
\]
be the principal annulus in the original dynamical plane, and let
\[
g_n:U_n\to V_n
\]
be the normalized quadratic-like renormalization at level \(n\).

The fundamental annulus of \(g_n\) is
\[
\mathcal A_n^{\mathrm{fund}}
:=
V_n\setminus \overline{U_n}.
\]

---

## Exact theorem requested

**Problem / Theorem.**  
Prove that for every \(n\ge 0\) there exists an affine biholomorphism
\[
\psi_n(z)=a_n z+b_n,\qquad a_n\neq 0,
\]
such that
\[
\psi_n\bigl(P_{Q_n}(c)\bigr)=V_n,
\qquad
\psi_n\bigl(P_{Q_{n+1}}(c)\bigr)=U_n.
\]

Consequently,
\[
\psi_n\bigl(A_n^{\mathrm{princ}}\bigr)=\mathcal A_n^{\mathrm{fund}}.
\]

Hence, by conformal invariance of modulus,
\[
\operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
=
\operatorname{mod}_{\mathrm{conf}}(\mathcal A_n^{\mathrm{fund}})
=
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n}).
\]

---

## Quantified form

\[
\forall c,\ \forall T,\ \forall n\ge 0,\ \exists a_n,b_n\in\mathbb C,\ a_n\neq 0,
\]
\[
\psi_n(z)=a_n z+b_n,\qquad
\psi_n(P_{Q_n}(c))=V_n,\qquad
\psi_n(P_{Q_{n+1}}(c))=U_n.
\]

---

## Role in the proof graph

This is the geometric identification step:

\[
\text{fundamental annulus modulus lower bound}
\Longrightarrow
\text{principal annulus modulus lower bound}.
\]

It is the exact structural input needed to transport the true conformal-modulus
estimate on the renormalized quadratic-like map back to the principal nest of
\(f_c\).
