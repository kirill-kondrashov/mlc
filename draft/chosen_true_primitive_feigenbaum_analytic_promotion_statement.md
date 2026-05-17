# Standalone theorem statement: `ChosenTruePrimitiveFeigenbaumAnalyticPromotionData`

## Informal Lean target

The repository constant

```lean
ChosenTruePrimitiveFeigenbaumAnalyticPromotionData
```

is intended to package the following mathematical theorem.

---

## Mathematical setting

Let

- \(f : U \to V\) be a quadratic-like map with connected Julia set,
- \(R^n f : U_n \to V_n\) denote its \(n\)-th quadratic-like renormalization,
- \(p_n \in \mathbb{N}\) denote the corresponding renormalization period,
- \(A_n^{\mathrm{fund}} := V_n \setminus \overline{U_n}\) denote the \(n\)-th fundamental annulus.

Assume that \(f\) is **primitive Feigenbaum of bounded type**, in the following sense:

1. **Infinitely renormalizable:** every renormalization \(R^n f\) is defined.
2. **Primitive:** every renormalization \(R^n f\) is primitive (not satellite).
3. **Bounded combinatorics:** there exists \(P \ge 2\) such that
   \[
   p_n \le P \qquad \text{for all } n \ge 0.
   \]

Let
\[
\mu_{\mathrm{true}}
\]
be the chosen true conformal modulus on annuli, i.e. the modulus attached to the distinguished conformal-modulus API instance underlying
`chosenTrueConformalModulus`.

For each \(n\), define the true fundamental modulus by
\[
\operatorname{mod}_{\mathrm{true}}^{\mathrm{fund}}(R^n f)
:=
\mu_{\mathrm{true}}\!\left(A_n^{\mathrm{fund}}\right).
\]

---

## Standalone theorem

**Theorem (Chosen true primitive-Feigenbaum analytic promotion).**
Let \(f\) be a primitive Feigenbaum quadratic-like map of bounded type. Then there exist constants
\[
N \in \mathbb{N}, \qquad \varepsilon > 0
\]
such that for all \(n \ge N\),
\[
\operatorname{mod}_{\mathrm{true}}^{\mathrm{fund}}(R^n f) \ge \varepsilon.
\]

Equivalently,
\[
\exists\, N \in \mathbb{N}\, \exists\, \varepsilon > 0 \text{ such that } \forall n \ge N,\;
\mu_{\mathrm{true}}\!\left(V_n \setminus \overline{U_n}\right) \ge \varepsilon.
\]

---

## Expanded hypothesis package

The theorem is meant to be applied after the following ingredients have been isolated formally.

### 1. Finite primitive combinatorics

Bounded primitive periods produce a finite set of primitive combinatorial types
\[
\mathcal{F} = \{\tau_1,\dots,\tau_m\}
\]
such that every renormalization \(R^n f\) has type \(\tau_n \in \mathcal{F}\).

### 2. Real a priori bounds

There exist uniform real-geometry constants depending only on \(\mathcal{F}\), giving bounded geometry for the principal nest / return domains attached to \(R^n f\) for all sufficiently large \(n\).

### 3. Complex promotion

Those real bounds promote to complex a priori bounds: there exists
\[
\varepsilon = \varepsilon(\mathcal{F}) > 0
\]
such that every sufficiently deep primitive renormalization with combinatorics in \(\mathcal{F}\) satisfies
\[
\mu_{\mathrm{true}}\!\left(V_n \setminus \overline{U_n}\right) \ge \varepsilon.
\]

The theorem `ChosenTruePrimitiveFeigenbaumAnalyticPromotionData` is the repository-level abstraction of exactly this Step 3 conclusion for the chosen true modulus.

---

## Relation to the current Lean route

This theorem is the true-modulus replacement for the older Gaussian-proxy analytic step. In the current repository architecture it is the missing proof obligation needed to pass from:

1. primitive bounded combinatorics, and
2. the chosen true conformal-modulus interface,

to

3. eventual positive lower bounds for the true fundamental moduli of all deep primitive Feigenbaum renormalizations.

Once available, it feeds the downstream route:

\[
\text{primitive Feigenbaum data}
\;\Longrightarrow\;
\text{eventual true fundamental modulus lower bound}
\;\Longrightarrow\;
\text{legacy bridge / primitive shrinkage / bounded-type constructive cutover}.
\]

---

## Short proof blueprint

The intended proof has the standard three-part structure:

1. **bounded primitive combinatorics \(\Rightarrow\) finite combinatorial family;**
2. **finite primitive family \(\Rightarrow\) uniform real bounds;**
3. **real bounds + primitiveness \(\Rightarrow\) uniform positive true conformal modulus of the fundamental annulus.**

The theorem above is precisely the packaged output of Step 3 for the distinguished modulus instance `chosenTrueConformalModulus`.
