# Standalone theorem statement: Lyubich-to-conformal bridge for primitive towers

## Repository target

This note formulates, in ordinary mathematical notation, the remaining axiom

```lean
MLC.lyubich_conformal_bridge
```

from `Mlc/PrimitiveModulusDivergence.lean`.

In the repository, this axiom is the missing bridge from the abstract
Lyubich-style lower-bound package on the **principal renormalization annuli**
to the concrete conformal-modulus divergence statement for the full quadratic
Yoccoz puzzle.

---

## Mathematical setting

Let
\[
f_c(z)=z^2+c,\qquad c\in\mathbb C,
\]
and let
\[
T=\{g_n\}_{n\ge 0}
\]
be a renormalization tower for \(f_c\). Write
\[
Q_n
\]
for the cumulative renormalization depths attached to the tower, so that the
corresponding principal-nest annuli in the dynamical plane of \(f_c\) are
\[
A_n^{\mathrm{princ}}
:=
\operatorname{DynPuzzlePiece}(c,Q_n,0)\setminus
\operatorname{DynPuzzlePiece}(c,Q_{n+1},0).
\]

Let
\[
\mu_{\mathrm{L}}(A_n^{\mathrm{princ}})
\]
denote the Lyubich modulus observable attached to the principal annulus
\(A_n^{\mathrm{princ}}\), and let
\[
\operatorname{mod}_{\mathrm{conf}}(\mathcal P_n)
\]
denote the conformal modulus of the full Yoccoz puzzle annulus
\[
\mathcal P_n
:=
\operatorname{PuzzlePiece}(c,n,0)\setminus \operatorname{PuzzlePiece}(c,n+1,0).
\]

In the current Lean file, the conclusion is encoded as non-summability of the
sequence \(n\mapsto \operatorname{cmodulus}(\mathcal P_n)\).

---

## Standalone theorem

**Theorem (Lyubich principal-nest divergence implies conformal puzzle divergence).**
Let \(c\in\mathbb C\), and let \(T\) be a renormalization tower for \(f_c\).
Assume that the Lyubich moduli of the principal-nest annuli along the tower are
not summable:
\[
\sum_{n=0}^{\infty}\mu_{\mathrm{L}}(A_n^{\mathrm{princ}})=+\infty.
\]
Equivalently,
\[
\neg\operatorname{Summable}\bigl(n\mapsto \mu_{\mathrm{L}}(A_n^{\mathrm{princ}})\bigr).
\]

Then the conformal moduli of the full Yoccoz puzzle annuli are also not
summable:
\[
\sum_{n=0}^{\infty}\operatorname{mod}_{\mathrm{conf}}(\mathcal P_n)=+\infty.
\]
Equivalently,
\[
\neg\operatorname{Summable}\bigl(n\mapsto \operatorname{mod}_{\mathrm{conf}}(\mathcal P_n)\bigr).
\]

---

## Equivalent quantified form

For every parameter \(c\) and every renormalization tower \(T\) of \(f_c\),
\[
\Bigl[
\neg\operatorname{Summable}\bigl(n\mapsto \mu_{\mathrm{L}}(A_n^{\mathrm{princ}})\bigr)
\Bigr]
\Longrightarrow
\Bigl[
\neg\operatorname{Summable}\bigl(n\mapsto \operatorname{mod}_{\mathrm{conf}}(\mathcal P_n)\bigr)
\Bigr].
\]

---

## Role in the proof graph

This theorem is exactly the missing non-tautological step needed to pass from
the primitive renormalization tower estimates to the standard Yoccoz shrinkage
criterion:

\[
\text{Lyubich / primitive principal-nest control}
\Longrightarrow
\text{full puzzle conformal divergence}
\Longrightarrow
\text{puzzle shrinkage}
\Longrightarrow
\text{local connectivity}.
\]

Without this bridge, the repository can still formulate lower bounds on
principal renormalization annuli, but it cannot convert them into the
non-summability statement used by the current conformal Yoccoz machinery.

---

## Proof blueprint for the conformal version

If one identifies the Lyubich modulus of the \(n\)-th principal annulus with the
exact block sum
\[
\mu_{\mathrm L}(A_n^{\mathrm{princ}})
:=
\sum_{k=Q_n}^{Q_{n+1}-1}\operatorname{mod}_{\mathrm{conf}}(\mathcal P_k),
\]
then the bridge reduces to a finite-block summation argument for a
non-negative series.

Write
\[
m_k := \operatorname{mod}_{\mathrm{conf}}(\mathcal P_k)\ge 0,
\qquad
L_n := \mu_{\mathrm L}(A_n^{\mathrm{princ}}).
\]
For every \(M\ge 1\),
\[
\sum_{n=0}^{M-1} L_n
=
\sum_{n=0}^{M-1}\sum_{k=Q_n}^{Q_{n+1}-1} m_k
=
\sum_{k=Q_0}^{Q_M-1} m_k,
\]
because the intervals \([Q_n,Q_{n+1})\) partition \([Q_0,Q_M)\).

Therefore, if \(\sum_k m_k\) were summable, then the block-sum series
\(\sum_n L_n\) would also be summable: its partial sums are bounded above by the
partial sums of the full non-negative series. Contrapositively,
\[
\neg \operatorname{Summable}(L_n)
\Longrightarrow
\neg \operatorname{Summable}(m_k).
\]

This is the exact mathematical content now implemented for the **conformal**
principal-annulus observable in the Lean code; the remaining gap in the current
repository is that the legacy symbol `LyubichModulus` is still a separate
constant proxy used by older placeholder routes.
