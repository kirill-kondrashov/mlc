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
