# Standalone problem: typewise Grötzsch promotion for primitive Feigenbaum towers

## Repository target

This note states the remaining theorem-data interface

```lean
PrimitiveFeigenbaumTypewiseGrotzschPromotionGlobalData
```

in standard mathematical notation.

---

## Mathematical setup

Retain the setup of a bounded-type primitive Feigenbaum renormalization tower
\[
T=(g_n)_{n\ge 0},\qquad g_n:U_n\to V_n,
\]
for
\[
f_c(z)=z^2+c.
\]

Let \(\tau_n\in \mathcal F_P\) be the primitive combinatorial type of the step
\[
g_n\rightsquigarrow g_{n+1},
\]
where \(\mathcal F_P\) is the finite set of primitive types of period at most
the global bound \(P\).

Assume the typewise real bounds of the previous problem are available, so that
for each \(\tau\in\mathcal F_P\) there is a strictly positive gap-ratio
constant
\[
C(\tau)>0.
\]

Let
\[
\mathcal A_n^{\mathrm{fund}}:=V_n\setminus \overline{U_n}
\]
be the fundamental annulus of the renormalized map \(g_n\), and let
\[
\operatorname{mod}_{\mathrm{conf}}(\mathcal A_n^{\mathrm{fund}})
\]
denote its conformal modulus.

---

## Exact theorem requested

**Problem / Theorem.**  
Prove that there exists a function
\[
\varepsilon:\mathcal F_P\to \mathbb R_{>0}
\]
such that for every sufficiently deep level \(n\),
\[
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})
\ge \varepsilon(\tau_n).
\]

Equivalently: there is a strictly positive typewise conformal-modulus lower
bound depending only on the primitive combinatorial type, obtained by promoting
the real gap ratio through the Teichmüller/Grötzsch extremal-ring estimate.

More explicitly, one seeks a positive function \(\Psi:\mathbb R_{>0}\to
\mathbb R_{>0}\) such that
\[
\varepsilon(\tau)=\Psi(C(\tau))
\]
and
\[
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})
\ge \Psi(C(\tau_n)).
\]

---

## Quantified form

\[
\forall c,\ \forall T,\ 
\bigl[\text{all renormalizations primitive}\bigr]
\wedge
\bigl[\text{periods uniformly bounded}\bigr]
\Longrightarrow
\exists \varepsilon:\mathcal F_P\to \mathbb R_{>0},
\]
\[
\exists N_0,\ \forall n\ge N_0,\qquad
\operatorname{mod}_{\mathrm{conf}}(V_n\setminus \overline{U_n})
\ge \varepsilon(\tau_n).
\]

---

## Role in the proof graph

This is the complex-analytic promotion step:

\[
\text{typewise real gap bounds}
\Longrightarrow
\text{typewise conformal modulus bounds}.
\]

Together with finiteness of \(\mathcal F_P\), it yields the uniform eventual
lower bound on the fundamental annulus modulus by taking a minimum over the
finite type set.
