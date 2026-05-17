# Standalone theorem statement: existence of a parameter-modeled fast fixed point

## Repository target

This note formulates, in ordinary mathematical notation, the remaining axiom

```lean
MLC.exists_parameter_model_rfast_fixed_point
```

from `Mlc/RenormalizationTowerExistence.lean`.

In the repository, this is the parameter-level bridge that turns an abstract
fast fixed point of the renormalization operator \(R_{\mathrm{fast}}\) into a
quadratic parameter \(c\) whose associated quadratic-like map is exactly that
fixed point.

---

## Mathematical setting

Let
\[
R_{\mathrm{fast}}:\mathcal B\to \mathcal B
\]
be the fast renormalization operator on the Banach / quadratic-like model space
\(\mathcal B\) used in the Molecule framework. Let
\[
\mathrm{Par}:\mathbb C\to \mathcal B,\qquad c\mapsto \mathrm{Par}(c),
\]
denote the parameter-model map that assigns to a quadratic parameter \(c\) its
normalized quadratic-like representative. In the Lean repository this is the
map
\[
c\mapsto \texttt{parameterToBMol}(c).
\]

Write
\[
g_\ast\in\mathcal B
\]
for a quadratic-like map. The conditions

1. \(R_{\mathrm{fast}}(g_\ast)=g_\ast\),
2. \(g_\ast\) is fast-renormalizable,

mean that \(g_\ast\) is a genuine fixed point of the renormalization operator
inside the fast-renormalizable locus.

---

## Standalone theorem

**Theorem (existence of a parameter-modeled fast renormalization fixed point).**
There exists a quadratic-like map \(g_\ast\) and a parameter \(c_\ast\in\mathbb
C\) such that
\[
R_{\mathrm{fast}}(g_\ast)=g_\ast,
\]
\[
g_\ast \text{ is fast-renormalizable},
\]
and
\[
g_\ast=\mathrm{Par}(c_\ast).
\]

Equivalently, there exists \(c_\ast\in\mathbb C\) such that the parameter model
\(\mathrm{Par}(c_\ast)\) is a fast fixed point of renormalization:
\[
R_{\mathrm{fast}}(\mathrm{Par}(c_\ast))=\mathrm{Par}(c_\ast),
\qquad
\mathrm{Par}(c_\ast)\ \text{is fast-renormalizable}.
\]

---

## Quantified form

\[
\exists g_\ast\in\mathcal B\ \exists c_\ast\in\mathbb C
\quad\text{such that}\quad
R_{\mathrm{fast}}(g_\ast)=g_\ast,
\]
\[
g_\ast\ \text{is fast-renormalizable},
\qquad
g_\ast=\mathrm{Par}(c_\ast).
\]

Equivalently,
\[
\exists c_\ast\in\mathbb C
\quad\text{such that}\quad
R_{\mathrm{fast}}(\mathrm{Par}(c_\ast))=\mathrm{Par}(c_\ast)
\]
and
\[
\mathrm{Par}(c_\ast)\ \text{is fast-renormalizable}.
\]

---

## Immediate consequence used in the repository

Once this theorem is known, the corresponding parameter \(c_\ast\) carries an
infinite renormalization tower:
\[
\exists c_\ast\in\mathbb C,\qquad
\text{there exists a renormalization tower for } \mathrm{Par}(c_\ast).
\]

This is exactly the input needed by the route

\[
\text{parameter-modeled fixed point}
\Longrightarrow
\text{tower existence}
\Longrightarrow
\text{IR local connectivity via the inconsistency route}
\Longrightarrow
\texttt{MLC.mlc\_conjecture}.
\]

---

## Why this theorem is nontrivial

The upstream Molecule package already provides an abstract fast fixed point
\(g_\ast\) of \(R_{\mathrm{fast}}\). What is still missing at the repository
level is the mathematical statement that this fixed point is actually realized
by a quadratic parameter:
\[
g_\ast=\mathrm{Par}(c_\ast)
\quad\text{for some } c_\ast\in\mathbb C.
\]

So this theorem is precisely the parameterization / modeling bridge from the
abstract renormalization fixed point to the quadratic family.
