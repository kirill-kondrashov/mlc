# Standalone theorem statement: the remaining external input for `ChosenTruePrimitiveFeigenbaumAnalyticPromotionData`

## Informal Lean target

After the recent refactor, the only genuinely missing mathematical input is no longer the finite-minimum step. That step is already formalized in the repository.

What remains to be proved externally is the theorem that supplies the **type-wise positive constants**
\[
\varepsilon_\tau > 0
\]
for bounded primitive combinatorics.

In the current Lean architecture, this missing input is captured by the theorem surface

```lean
PrimitiveFeigenbaumTypewiseTrueFundamentalGlobalData μApi
```

and, for the chosen true modulus, it feeds

```lean
chosenTruePrimitiveFeigenbaumAnalyticPromotion_of_typewiseData
```

which then yields

```lean
ChosenTruePrimitiveFeigenbaumAnalyticPromotionData hμ.
```

---

## Mathematical setting

Let

- \(f : U \to V\) be a quadratic-like map with connected Julia set,
- \(R^n f : U_n \to V_n\) denote the \(n\)-th quadratic-like renormalization,
- \(p_n\) denote the renormalization period of \(R^n f \to R^{n+1} f\),
- \(\tau_n\) denote the primitive combinatorial type of the \(n\)-th renormalization,
- \(A_n^{\mathrm{fund}} := V_n \setminus \overline{U_n}\) denote the \(n\)-th fundamental annulus.

Assume:

1. **Infinite renormalizability:** \(R^n f\) is defined for all \(n \ge 0\).
2. **Bounded type:** there exists \(P \ge 2\) such that \(p_n \le P\) for all \(n\).
3. **Strict primitiveness:** every renormalization \(R^n f\) is primitive.

Let
\[
\mu_{\mathrm{true}}
\]
be the chosen true conformal modulus on annuli.

Let
\[
\mathcal F
\]
be the finite family of primitive combinatorial types arising from the bounded-type hypothesis. In the current repository, \(\mathcal F\) is the eventual image of the tower under the actual combinatorial-type map \(n \mapsto \tau_n\).

---

## Standalone theorem to prove

**Theorem (type-wise true a priori bounds for bounded primitive Feigenbaum towers).**
Let \(f\) be a primitive Feigenbaum quadratic-like map of bounded type, and let \(\mathcal F\) be the corresponding finite family of primitive combinatorial types. Then there exists a function
\[
\tau \mapsto \varepsilon_\tau \in \mathbb R_{>0}
\qquad (\tau \in \mathcal F)
\]
and an index \(N \in \mathbb N\) such that for every \(n \ge N\),

1. the combinatorial type \(\tau_n\) of \(R^n f\) belongs to \(\mathcal F\), and
2. the true conformal modulus of the fundamental annulus satisfies
   \[
   \mu_{\mathrm{true}}\!\left(A_n^{\mathrm{fund}}\right)
   =
   \mu_{\mathrm{true}}\!\left(V_n \setminus \overline{U_n}\right)
   \ge
   \varepsilon_{\tau_n}.
   \]

Equivalently,
\[
\exists\, N \in \mathbb N,\;
\exists\, (\varepsilon_\tau)_{\tau \in \mathcal F},
\quad
\forall \tau \in \mathcal F,\; \varepsilon_\tau > 0,
\]
such that for all \(n \ge N\),
\[
\tau_n \in \mathcal F
\quad\text{and}\quad
\mu_{\mathrm{true}}\!\left(V_n \setminus \overline{U_n}\right) \ge \varepsilon_{\tau_n}.
\]

---

## Why this is exactly the remaining blocker

The repository now already proves the following reduction:

1. bounded periods give a finite family \(\mathcal F\) of **actual tower combinatorial types**;
2. if one has type-wise bounds \(\varepsilon_\tau > 0\) for \(\tau \in \mathcal F\);
3. then taking the finite minimum
   \[
   \varepsilon := \min_{\tau \in \mathcal F} \varepsilon_\tau
   \]
   yields a uniform eventual lower bound
   \[
   \mu_{\mathrm{true}}\!\left(V_n \setminus \overline{U_n}\right) \ge \varepsilon
   \qquad (n \gg 1),
   \]
   which is exactly the content of `ChosenTruePrimitiveFeigenbaumAnalyticPromotionData`.

So the only missing mathematics is the theorem above that **constructs the per-type constants \(\varepsilon_\tau\)** from real/complex bounds.

---

## Expected proof structure

This theorem should be proved by the usual two-stage analytic route.

### 1. Real a priori bounds

Bounded primitive combinatorics imply bounded geometry for the real principal nest. Concretely, there is a depth \(N_0\) and a constant \(C>0\), depending only on the finite family \(\mathcal F\), such that for all \(n \ge N_0\):

- the return interval \(I_{n+1}\) is uniformly well inside \(I_n\), and
- the adjacent real gaps next to \(I_{n+1}\) are bounded below by \(C |I_{n+1}|\).

### 2. Complex promotion

Using Teichmuller / Grotzsch extremal-length estimates and primitiveness, the gap bound promotes to a lower bound on the true conformal modulus of the fundamental annulus. For each type \(\tau \in \mathcal F\), this yields a constant
\[
\varepsilon_\tau > 0
\]
depending only on the bounded geometry data attached to \(\tau\), such that whenever \(R^n f\) has type \(\tau\),
\[
\mu_{\mathrm{true}}\!\left(V_n \setminus \overline{U_n}\right) \ge \varepsilon_\tau.
\]

The finite-minimum argument is then purely formal and is already implemented in Lean.

---

## Repository-level role

This theorem is the remaining outsourced mathematical statement needed to complete the chosen true-modulus analytic-promotion route.

Once supplied, the current Lean route is:

\[
\text{bounded periods}
\Longrightarrow
\text{finite actual tower combinatorics}
\Longrightarrow
\text{type-wise true bounds } \varepsilon_\tau
\Longrightarrow
\text{uniform eventual true lower bound}
\Longrightarrow
\texttt{ChosenTruePrimitiveFeigenbaumAnalyticPromotionData}.
\]
