# Standalone theorem statement: primitive towers force principal-annulus conformal divergence

## Repository target

After theoremizing the finite-block conformal bridge, the remaining mathematical
gap in the primitive route is no longer the passage

\[
\text{principal annulus conformal divergence}
\Longrightarrow
\text{full puzzle conformal divergence}.
\]

That step is now available. The missing theorem is the **upstream primitive
input** that should produce non-summability of the actual conformal moduli of
the tower-selected principal annuli.

In repository terms, this is the sentence needed to replace the current proxy
lemma

```lean
primitive_modulus_divergence
```

which still uses the placeholder observable `LyubichModulus = 1`.

---

## Mathematical setting

Let
\[
f_c(z)=z^2+c,\qquad c\in\mathbb C,
\]
and let
\[
T=(g_n)_{n\ge 0}
\]
be a renormalization tower for \(f_c\). Let
\[
Q_n
\]
denote the cumulative renormalization depths of the tower. For each \(n\), let
\[
A_n^{\mathrm{princ}}
:=
P_{Q_n}(c)\setminus P_{Q_{n+1}}(c)
\]
be the corresponding principal annulus between the dynamical puzzle pieces
\(P_{Q_n}(c)\) and \(P_{Q_{n+1}}(c)\).

Assume that the tower has infinitely many primitive renormalization levels, i.e.
\[
\{n\in\mathbb N : \text{the renormalization } g_n \rightsquigarrow g_{n+1}
\text{ is primitive}\}
\]
is infinite.

---

## Standalone theorem

**Theorem (primitive renormalization forces principal-annulus conformal
divergence).**  
Let \(c\in\mathbb C\), and let \(T\) be a renormalization tower for \(f_c\) with
infinitely many primitive levels. Then the conformal moduli of the associated
principal annuli are not summable:
\[
\sum_{n=0}^{\infty}\operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
=+\infty.
\]
Equivalently,
\[
\neg \operatorname{Summable}\Bigl(
n\mapsto \operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
\Bigr).
\]

---

## Equivalent quantified form

For every \(c\in\mathbb C\) and every renormalization tower \(T\) of \(f_c\),
\[
\Bigl[
\{n\in\mathbb N : T_n \text{ is primitive}\}\text{ is infinite}
\Bigr]
\Longrightarrow
\Bigl[
\neg \operatorname{Summable}\bigl(
n\mapsto \operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
\bigr)
\Bigr].
\]

---

## Role in the proof graph

Combined with the now-theoremized finite-block conformal bridge, this statement
would yield:

\[
\text{infinitely many primitive levels}
\Longrightarrow
\text{principal-annulus conformal divergence}
\Longrightarrow
\text{full puzzle conformal divergence}
\Longrightarrow
\text{puzzle shrinkage}
\Longrightarrow
\text{local connectivity}.
\]

So this is the clean remaining mathematical sentence that replaces the old proxy
step and turns the primitive branch into a genuine conformal-modulus argument.

---

## Proof blueprint

The proof splits into four standard analytic ingredients.

### 1. Universal complex bounds on primitive levels

There exist constants
\[
\mu_0>0,\qquad N_0\in\mathbb N,
\]
such that whenever \(n\ge N_0\) is a primitive renormalization level, the
normalized quadratic-like map
\[
g_n:U_n\to V_n
\]
has fundamental annulus of uniformly positive conformal modulus:
\[
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})\ge \mu_0.
\]

This is the actual Lyubich primitive complex-bounds input: primitiveness forces
a definite macroscopic separation of the little Julia sets, uniformly across all
sufficiently deep primitive levels.

### 2. Conformal identification with the principal annulus

By construction, the renormalized map \(g_n\) is obtained from an iterate of
\(f_c\) on the principal nest by an affine normalization
\[
\psi_n(z)=a_n z+b_n.
\]
This normalization identifies the principal nest pieces with the normalized
quadratic-like domains:
\[
\psi_n(P_{Q_n}(c))=V_n,\qquad \psi_n(P_{Q_{n+1}}(c))=U_n.
\]
Since affine maps are biholomorphic, they preserve conformal modulus exactly.
Hence for every primitive level \(n\ge N_0\),
\[
\operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
=
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})
\ge \mu_0.
\]

### 3. Non-negativity

For every \(n\),
\[
\operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})\ge 0.
\]

### 4. Divergence of the non-negative series

Let
\[
\mathcal N_{\mathrm{prim}}
=
\{n\in\mathbb N : g_n\rightsquigarrow g_{n+1}\text{ is primitive}\}.
\]
By hypothesis, \(\mathcal N_{\mathrm{prim}}\) is infinite, so
\[
\mathcal N_{\mathrm{prim}}^\ast
:=
\mathcal N_{\mathrm{prim}}\cap [N_0,\infty)
\]
is still infinite. For every \(n\in \mathcal N_{\mathrm{prim}}^\ast\),
\[
\operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})\ge \mu_0.
\]
Thus the series
\[
\sum_{n=0}^{\infty}\operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
\]
contains infinitely many terms bounded below by the same positive constant
\(\mu_0\). Since all terms are non-negative, the series diverges to \(+\infty\).

---

## Lean-facing decomposition

To formalize this proof in the repository, the remaining primitive package
should be split into the following theorem-sized inputs:

1. **Primitive complex bounds**
   \[
   \exists \mu_0>0,\ \exists N_0,\ \forall n\ge N_0,\ 
   n\in\mathcal N_{\mathrm{prim}}
   \Rightarrow
   \operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})\ge \mu_0.
   \]
2. **Affine comparison / normalization**
   \[
   \operatorname{mod}_{\mathrm{conf}}(A_n^{\mathrm{princ}})
   =
   \operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n}).
   \]
3. **Real-analysis lemma**
   a non-negative series with infinitely many terms \(\ge \mu_0>0\) is not
   summable.

Once these are available, the old proxy path

```lean
LyubichModulus = 1
```

can be deleted from the primitive branch and replaced by an actual conformal
proof:

\[
\text{primitive levels infinitely often}
\Longrightarrow
\text{principal-annulus conformal divergence}
\Longrightarrow
\text{full puzzle conformal divergence}
\Longrightarrow
\text{local connectivity}.
\]
