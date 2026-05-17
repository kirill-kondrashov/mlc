# Expert problem statement: Step 1 primitive complex bounds for the Feigenbaum route

## Purpose

This note isolates **Step 1** of the remaining primitive proof pipeline in a
standalone form suitable to ask a human expert. It is the exact analytic input
still missing after the affine-normalization and finite-block summation steps
have been theoremized in Lean.

In repository terms, this is the missing theorem surface behind the global datum

```lean
PrimitiveFeigenbaumTrueFundamentalLowerBoundGlobalData
```

for a genuine conformal-modulus API.

---

## Mathematical setup

Let
\[
f_c(z)=z^2+c,\qquad c\in\mathbb C.
\]

Let
\[
T=(g_n)_{n\ge 0}
\]
be a renormalization tower associated to \(f_c\), where each renormalized map
\[
g_n:U_n\to V_n
\]
is a quadratic-like map obtained from a suitable iterate of \(f_c\) by affine
normalization.

Assume the tower is **primitive Feigenbaum of bounded type**, in the following
sense:

1. every renormalization step is primitive:
   \[
   g_n \rightsquigarrow g_{n+1}\ \text{is primitive for all }n\ge 0;
   \]
2. the renormalization periods are uniformly bounded, i.e. there exists
   \(P\in\mathbb N\) such that every relative renormalization period \(p_n\) of
   the step \(g_n\rightsquigarrow g_{n+1}\) satisfies
   \[
   p_n\le P \qquad \text{for all }n\ge 0.
   \]

For each \(n\), define the normalized fundamental annulus
\[
\mathcal A_n^{\mathrm{fund}}
:=
V_n\setminus \overline{U_n}.
\]

Let
\[
\operatorname{mod}_{\mathrm{conf}}(\mathcal A_n^{\mathrm{fund}})
\]
denote its conformal modulus.

---

## Exact theorem requested

**Problem / Theorem.**  
Under the assumptions above, prove that there exist constants
\[
\mu_0>0,\qquad N_0\in\mathbb N
\]
such that for every \(n\ge N_0\),
\[
\operatorname{mod}_{\mathrm{conf}}(\mathcal A_n^{\mathrm{fund}})
=
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})
\ge \mu_0.
\]

Equivalently: the fundamental annuli of a bounded-type primitive Feigenbaum
tower are eventually bounded away from degeneration by a uniform positive
conformal-modulus constant.

---

## Stronger variant also welcome

If available from the literature, an even stronger theorem would also solve the
Lean need:

\[
\exists \mu_0>0,\ \forall n\ge 0,\qquad
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})\ge \mu_0.
\]

But the repository only needs the **eventual** form with some transient depth
\(N_0\).

---

## Why this is the exact remaining Step 1 input

The downstream steps are already separated out:

1. **Affine normalization comparison** identifies the principal annulus in the
   original dynamical plane with the normalized fundamental annulus.
2. **Real-analysis / divergence** then converts a uniform lower bound into
   non-summability of principal-annulus moduli.
3. **Finite-block conformal bridge** converts principal-annulus divergence into
   full puzzle conformal divergence.
4. **Yoccoz puzzle shrinkage** gives local connectivity.

So the remaining expert-facing question is precisely the existence of the
uniform lower bound above.

---

## Lean-facing translation

A proof of the theorem above should discharge the following theorem surface:

\[
\forall c,\ \forall T,\ 
\bigl[\text{bounded periods}\bigr]
\wedge
\bigl[\text{all renormalizations primitive}\bigr]
\Longrightarrow
\exists \mu_0>0,\ \exists N_0,\ \forall n\ge N_0,\ 
\mu_0 \le
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n}).
\]

This is exactly the mathematical content needed to instantiate the Lean datum
`PrimitiveFeigenbaumTrueFundamentalLowerBoundData` globally.
