# Standalone problem: bridge from true conformal modulus to the legacy primitive consumer

## Repository target

This note states the remaining theorem-data interface

```lean
ChosenTrueToLegacyPrimitiveEventualBridgeData
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

Let
\[
A_n^{\mathrm{princ}}
:=
P_{Q_n}(c)\setminus P_{Q_{n+1}}(c)
\]
be the principal annulus.

Assume we are given a genuine conformal-modulus observable
\[
\mu_{\mathrm{true}}(\,\cdot\,)
\]
on annulus-like sets, satisfying affine invariance and non-negativity. Assume
also that there exist constants
\[
\mu_0>0,\qquad N_0\in\mathbb N
\]
such that for every \(n\ge N_0\),
\[
\mu_0 \le \mu_{\mathrm{true}}(A_n^{\mathrm{princ}}).
\]

The current legacy primitive consumer in the repository is phrased using the
existing proxy observable
\[
\operatorname{cmodulus}(A_n^{\mathrm{princ}}).
\]

---

## Exact theorem requested

**Problem / Theorem.**  
Prove that an eventual positive lower bound for the genuine conformal-modulus
observable on principal annuli implies an eventual positive lower bound for the
legacy observable:

there exist constants
\[
\mu_1>0,\qquad N_1\in\mathbb N
\]
such that for every \(n\ge N_1\),
\[
\mu_1 \le \operatorname{cmodulus}(A_n^{\mathrm{princ}}).
\]

In the strongest desirable form, one would have a comparison inequality
\[
\operatorname{cmodulus}(A)\ge \Phi\bigl(\mu_{\mathrm{true}}(A)\bigr)
\]
for annuli \(A\) in the principal-nest class, where \(\Phi:\mathbb R_{>0}\to
\mathbb R_{>0}\) is a positive comparison function. The theorem above would then
follow immediately.

---

## Quantified form

\[
\forall c,\ \forall T,\ 
\Bigl[
\exists \mu_0>0,\ \exists N_0,\ \forall n\ge N_0,\ 
\mu_0\le \mu_{\mathrm{true}}(A_n^{\mathrm{princ}})
\Bigr]
\Longrightarrow
\]
\[
\Bigl[
\exists \mu_1>0,\ \exists N_1,\ \forall n\ge N_1,\ 
\mu_1\le \operatorname{cmodulus}(A_n^{\mathrm{princ}})
\Bigr].
\]

---

## Role in the proof graph

This is the final migration bridge from the theoremized true-modulus route back
to the current legacy consumer path. Once this bridge is supplied, the chosen
true-modulus primitive Feigenbaum route can feed directly into the existing
primitive local-connectivity and bounded-type constructive theorems without any
further refactoring.
