# A counterexample to `MLC.green_sublevel_intersection_categorical`

**Result: the requested affirmative statement is false with the definitions in
this repository.** This document gives a rigorous proof of its negation,
including the complete finite arithmetic certificate needed for further Lean
formalisation. An affirmative proof cannot be supplied without an inconsistent
assumption.

The counterexample is

\[
\boxed{c=i,\qquad n=16.}
\]

Put

\[
A=\{p\in\mathbb C:G_i(p-i)<2^{-16}\},\qquad S=A\cap M.
\]

Both \(0\) and \(i\) belong to \(S\), whereas

\[
S\cap\{p:\operatorname{Im}p=45/64\}=\varnothing.
\]

Thus \(S\) is disconnected. Also \(2i\in A\setminus M\), so this example
satisfies the axiom's non-factorisation hypothesis.

**Verification status.** The mathematical proof below is complete, with its
finite arithmetic justified by the explicit certificate in Appendix A. Lean
4.28.0 has checked that entire arithmetic certificate with `by decide` and
reported **no axioms**. A separate implementation using exact rational
arithmetic and a different rounding precision also verified every interval.
The real/complex soundness of the interval operations is proved below in
mathematical prose; that soundness proof and its assembly into a Lean theorem
of the negation still need formalisation. The analytic and topological helper
theorems in Appendix B were also checked in Lean. This document does not claim
that Lean has already checked the complete negation.

Repository inspected: `/home/kir/pers/mlc`, commit
`adacab1f4f5a8fd6d2ee5fce79684b864abbdfd6`, on 2026-09-08. No existing Lean
source or axiom declaration was changed.

## 1. The exact statement being refuted

The definitions in
[`Mlc/ParaPuzzleConnectivity.lean`](../Mlc/ParaPuzzleConnectivity.lean) and
[`Mlc/CategoricalTopologicalApproximation.lean`](../Mlc/CategoricalTopologicalApproximation.lean)
give

\[
\begin{aligned}
f_c(z)&=z^2+c,\\
F_c^m(z)&=f_c^{\circ m}(z),\\
M&=\{c:(F_c^m(0))_{m\ge0}\text{ is bounded}\},\\
K_c&=\{z:(F_c^m(z))_{m\ge0}\text{ is bounded}\},\\
G_c(z)&=\lim_{m\to\infty}2^{-m}
  \log\max(1,|F_c^m(z)|),\\
A(c,n)&=\{p:G_c(p-c)<(1/2)^n\}.
\end{aligned}
\]

Existence of this limit is already proved by
`MLC.Quadratic.green_function_eq_lim`. In particular, the Green-function
normalisation here is exactly the repository's normalisation.

The categorical statement is

```lean
def MLC.GreenSublevelIntersectionCategoricalData : Prop :=
  ∀ (c : ℂ) (_hc : c ∈ MLC.Quadratic.MandelbrotSet) (n : ℕ),
    ¬ MLC.Categorical.factorsThrough
      (MLC.greenSublevelApproximation c n) MLC.mandelbrotApproximation →
    MLC.Categorical.ImageConnected
      (MLC.Categorical.intersection
        (MLC.greenSublevelApproximation c n) MLC.mandelbrotApproximation)
```

For inclusions of sets into the ambient plane, the already proved lemmas
`factorsThrough_ofSet_iff`, `image_intersection`, and `image_ofSet` say precisely
that

\[
\begin{aligned}
\operatorname{factorsThrough}(\operatorname{ofSet}B,
  \operatorname{ofSet}C)&\iff B\subseteq C,\\
\operatorname{image}(\operatorname{intersection}
  (\operatorname{ofSet}B,\operatorname{ofSet}C))&=B\cap C.
\end{aligned}
\]

Consequently the target is equivalent to

\[
\forall c\in M\ \forall n\in\mathbb N,\qquad
A(c,n)\not\subseteq M\Longrightarrow A(c,n)\cap M
\text{ is connected}.
\tag{1}
\]

This equivalence is also implemented as
`MLC.greenSublevelIntersectionCategoricalData_iff`. Its proof does not use
the axiom being refuted. The categorical formulation therefore cannot remove
a counterexample to (1).

## 2. Elementary orbit facts

### Lemma 2.1: the universal Mandelbrot orbit bound

If \(p\in M\), then \(|p|\le2\), and

\[
|F_p^m(0)|\le2\qquad(m\ge0).
\tag{2}
\]

**Proof.** First suppose \(C=|p|>2\). Whenever \(|w|\ge C\),

\[
|w^2+p|\ge |w|^2-C
\ge |w|^2-|w|
\ge(C-1)|w|.
\]

Since \(C-1>1\) and \(F_p^1(0)=p\), induction gives
\(|F_p^m(0)|\ge C(C-1)^{m-1}\) for \(m\ge1\). This is unbounded, a
contradiction. Thus \(|p|\le2\).

Now suppose an iterate has modulus \(r>2\). Put
\(\lambda=r-2/r>1\). Whenever \(t\ge r\),

\[
t^2-2\ge(r-2/r)t=\lambda t;
\]

indeed, \(t^2-rt\ge0\) and \(2t/r-2\ge0\). The reverse triangle inequality
and \(|p|\le2\) show that subsequent moduli grow at least geometrically
by the factor \(\lambda\). This again contradicts boundedness. This proves
(2). \(\square\)

The repository versions are `Molecule.mandelbrot_subset_ball` and
`Molecule.mandelbrot_eq_inter`, in
`.lake/packages/molecule-conjecture/Molecule/Mol.lean`.

### Lemma 2.2: explicit bounded and escaping orbits

We have

\[
0,i\in M,\qquad 0,i,-i\in K_i,\qquad 2i\notin M.
\tag{3}
\]

**Proof.** For parameter zero, the critical orbit is constantly zero. For
parameter \(i\), the critical orbit is

\[
0\longmapsto i\longmapsto -1+i\longmapsto -i
\longmapsto -1+i\longmapsto -i\longmapsto\cdots.
\]

These equalities follow by squaring. The two points \(-1+i\) and \(-i\)
form a two-cycle, and all displayed moduli are at most \(\sqrt2\). The
orbits starting at \(0,i,-i\) are therefore bounded. For parameter \(2i\),
the first two critical iterates are \(2i\) and \(-4+2i\); the latter has
squared modulus \(20>4\). Lemma 2.1 excludes \(2i\) from \(M\).
\(\square\)

### Lemma 2.3: bounded orbits have Green value zero

If \((F_c^m(z))\) is bounded, then \(G_c(z)=0\).

**Proof.** Choose a bound \(B\ge1\) for the moduli. Then

\[
0\le2^{-m}\log\max(1,|F_c^m(z)|)\le2^{-m}\log B\longrightarrow0.
\]

Take the limit defining \(G_c\). \(\square\)

This is also the implication from filled-Julia membership to Green value
zero in `MLC.Quadratic.green_function_eq_zero_iff_mem_K`, whose equivalence
is oriented as `G_c(z) = 0 ↔ z ∈ K c`.

It follows from (3) that for every natural number \(n\),

\[
0,i\in A(i,n)\cap M,\qquad 2i\in A(i,n)\setminus M.
\tag{4}
\]

For the three Green values in (4), the starting dynamical points \(p-i\)
are respectively \(-i,0,i\). Each has Green value zero, and
\((1/2)^n>0\).

## 3. A quantitative Green-function lower bound

### Lemma 3.1

If \(|w|>4\), then \(G_i(w)>1/2\).

**Proof.** Set \(r_m=|F_i^m(w)|\) and \(a=|w|/2>2\). The reverse triangle
inequality gives

\[
r_{m+1}\ge r_m^2-1\ge r_m^2/2\qquad\text{whenever }r_m\ge4.
\]

Induction yields

\[
r_m\ge2a^{2^m}>4\qquad(m\ge0).
\]

For the induction step, square the lower bound and divide by two. Taking
logarithms, dividing by \(2^m\), and passing to the defining limit gives

\[
G_i(w)\ge\log a=\log(|w|/2)>\log2>1/2.
\]

For completeness, \(\log2>1/2\) follows from
\(\log2=\int_1^2dt/t\): the integrand is at least \(1/2\) on that interval
and strictly larger on its interior. It can also be obtained directly from
Mathlib's proved bound `Real.log_two_gt_d9`. \(\square\)

### Lemma 3.2

For every \(k\in\mathbb N\),

\[
G_i(F_i^k(z))=2^kG_i(z).
\tag{5}
\]

**Proof.** The sequence defining the left side has its \(m\)-th term equal
to \(2^k\) times the \((m+k)\)-th term of the sequence defining \(G_i(z)\).
A fixed shift preserves the limit, and multiplication by \(2^k\) commutes
with taking the limit. \(\square\)

Equation (5) is `MLC.Quadratic.green_function_iterate`.

### Corollary 3.3

If \(k\le15\) and \(|F_i^k(z)|>4\), then

\[
G_i(z)>2^{-(k+1)}\ge2^{-16}.
\tag{6}
\]

**Proof.** Combine Lemma 3.1 and (5), then divide by the positive number
\(2^k\). The last inequality uses \(k+1\le16\). \(\square\)

Appendix B contains a checked Lean proof of (6). It uses the repository's
existing bound `green_function_bdd_below_log` in place of the elementary
growth proof above: `escape_bound I = 2` gives
\(G_i(w)\ge\log|w|-1/2\), which also implies the needed inequality when
\(|w|>4\).

## 4. The finite separation lemma

Put \(b=45/64\). The only substantial finite calculation needed is the
following precisely quantified assertion.

### Lemma 4.1

For every real \(x\in[-2,2]\), put \(p=x+bi\). At least one of the following
holds:

\[
\begin{array}{ll}
\text{(P)}&\exists k\in\{1,\ldots,16\},\quad |F_p^k(0)|>2;\\[2mm]
\text{(D)}&\exists k\in\{1,\ldots,15\},\quad |F_i^k(p-i)|>4.
\end{array}
\tag{7}
\]

**Proof by the explicit finite certificate in Appendix A.** We first prove
the soundness of the interval calculation, then explain the finite result.

### 4.2. Exact interval semantics and rounding

Let \(D=2^{48}=281474976710656\). An integer pair \((l,u)\) represents the
closed real interval

\[
\llbracket(l,u)\rrbracket=[l/D,u/D].
\]

An interval box \((X,Y)\) represents the complex numbers whose real part
belongs to \(\llbracket X\rrbracket\) and whose imaginary part belongs to
\(\llbracket Y\rrbracket\).

For an integer \(a\), write

\[
\operatorname{floorD}(a)=\lfloor a/D\rfloor,\qquad
\operatorname{ceilD}(a)=-\lfloor-a/D\rfloor.
\]

Since \(D>0\),

\[
\frac{\operatorname{floorD}(a)}D\le\frac a{D^2}
\le\frac{\operatorname{ceilD}(a)}D.
\tag{8}
\]

Lean's integer division by the positive integer `scale` is the floor
division used here, including for negative numerators.

For intervals \(X=(l,u)\), \(Y=(r,s)\), the operations in Appendix A have
the following meanings.

1. `add X Y = (l+r,u+s)` and `sub X Y = (l-s,u-r)` enclose addition and
   subtraction exactly.
2. For multiplication, the smallest and largest of \(lr,ls,ur,us\) are
   rounded outward using `floorD` and `ceilD`. The product of two elements
   of real intervals lies between the four endpoint products. One way to
   see this is to fix one factor, use linearity in the other, and then do
   the same for the remaining factor. Equation (8) preserves both bounds.
3. For `sq X`, the unrounded lower numerator is zero if \(l\le0\le u\),
   and otherwise \(\min(l^2,u^2)\); the upper numerator is
   \(\max(l^2,u^2)\). These are exactly the extrema of the square function
   on the interval, before outward rounding. Thus `sq X` encloses the
   square of every element of \(X\).

Every operation preserves ordered endpoints when its input intervals have
ordered endpoints. This follows either directly from these formulas or from
their enclosing a nonempty interval with its lower and upper bounds in the
stated order. All starting intervals in the certificate have ordered
endpoints.

### 4.3. Soundness for complex iteration

Write \(z=x+yi\), \(c=a+di\). Then

\[
z^2+c=(x^2-y^2+a)+(2xy+d)i.
\]

Accordingly, `step (X,Y) (A,B)` encloses \(z^2+c\) whenever the two input
boxes enclose \(z\) and \(c\). This follows immediately from the soundness
of `add`, `sub`, `mul`, and `sq` just proved. In particular, using the same
interval for two correlated quantities only enlarges an enclosure; it
does not invalidate it.

Induction on \(k\) now proves that `iterateBox C k Z` encloses \(F_c^k(z)\)
for every fixed \(c\) enclosed by \(C\) and starting point \(z\) enclosed
by \(Z\). Although a parameter interval is reused at every step, the
induction is for an arbitrary fixed parameter in that interval, so no
assumption that the parameter changes along its orbit is made.

If a box \((X,Y)\) encloses \(w\), the integer

```lean
normLower (X,Y) = (sq X).1 + (sq Y).1
```

satisfies

\[
\frac{\operatorname{normLower}(X,Y)}D
\le (\operatorname{Re}w)^2+(\operatorname{Im}w)^2=|w|^2.
\tag{9}
\]

Thus `normLower > 4 * D` proves \(|w|>2\), and
`normLower > 16 * D` proves \(|w|>4\). The inequalities are strict, as
required in (7).

### 4.4. Meaning of each certificate row

A row `(l, r, parameter, k)` covers the entire closed interval

\[
[l/16384,r/16384].
\]

The endpoint denominator is \(16384\), whereas the working interval scale
is \(D\). These are different quantities. Since \(16384\) and \(64\)
divide \(D\), all input endpoints and \(b\) are represented exactly.

For `parameter = true`, `checkCell` starts at the zero box and iterates
with the parameter box

\[
[l/16384,r/16384]+(45/64)i.
\]

It checks \(1\le k\le16\) and that the resulting `normLower` is strictly
greater than \(4D\). By (9), every real \(x\) in this interval satisfies
alternative (P).

For `parameter = false`, it instead iterates the fixed map \(f_i\), starting
from the box

\[
[l/16384,r/16384]+(45/64-1)i.
\]

It checks \(1\le k\le15\) and `normLower > 16 * D`. Every real \(x\) in
this interval therefore satisfies alternative (D).

### 4.5. Coverage and the verified finite result

The certificate lists **298 intervals**, comprising **150 parameter rows**
and **148 dynamical rows**. The intervals have adjacent endpoints, start
at \(-32768/16384=-2\), and end at \(32768/16384=2\).

The predicate `coverFrom (-32768) cells` checks the starting endpoint,
strict ordering of the endpoints in every row, equality of each row's
right endpoint to the next row's left endpoint, and the final endpoint.
For a precise induction invariant, if `coverFrom a rows = true`, then
every point of \([a,32768]\) either equals \(a\) or lies in a row interval
(before division by \(16384\)). For an empty list the checked equality
\(a=32768\) proves this invariant. For a first row \([a,r]\), a point
\(x\le r\) belongs to that row. A point \(x>r\) belongs to \([r,32768]\);
the induction hypothesis on the tail places it in a tail interval, since
\(x\ne r\). Finally, this certificate is nonempty, so its starting point
also belongs to its first interval. This proves coverage of the entire
closed interval. In particular, both global endpoints and every shared
endpoint are included.

The theorem checked in Appendix A is exactly

```lean
coverFrom (-32768) cells = true ∧ cells.all checkCell = true
```

The second conjunct asserts the strict escape inequality for every row;
the first guarantees that every \(x\in[-2,2]\) is covered by at least one
of those rows. The soundness arguments above therefore prove (7) for
every real \(x\), including all interval endpoints. This completes the
proof of Lemma 4.1. \(\square\)

This is a finite proof by exact integer inequalities. It does not infer
membership in either \(M\) or \(K_i\) from a finite non-escaping orbit,
and it does not infer the topology of a set from a sampled picture.

## 5. Exclusion of the horizontal line

### Lemma 5.1

If \(p\in M\) and \(\operatorname{Im}p=45/64\), then

\[
G_i(p-i)>2^{-16}.
\tag{10}
\]

**Proof.** Let \(x=\operatorname{Re}p\). By Lemma 2.1,
\(|x|\le|p|\le2\), and \(p=x+(45/64)i\). Apply Lemma 4.1.
Alternative (P) contradicts (2), so (D) holds: there is a \(k\le15\)
such that \(|F_i^k(p-i)|>4\). Corollary 3.3 gives (10).
\(\square\)

Taking \(A=A(i,16)\) and \(S=A\cap M\), equation (10) proves

\[
S\cap\{p:\operatorname{Im}p=45/64\}=\varnothing,
\tag{11}
\]

because membership in \(A\) requires the strictly opposite Green
inequality \(G_i(p-i)<2^{-16}\).

## 6. Disconnectedness and the straddling hypothesis

Define the two subsets of \(S\)

\[
S_- = S\cap\{p:\operatorname{Im}p<45/64\},\qquad
S_+ = S\cap\{p:\operatorname{Im}p>45/64\}.
\]

They are relatively open in \(S\), because the imaginary-part map is
continuous and the two strict half-lines are open. They are disjoint.
Equation (11) and trichotomy of the real order imply \(S=S_-\cup S_+\).
By (4), \(0\in S_-\) and \(i\in S_+\), since \(0<45/64<1\).

Thus \(S_-,S_+\) are a separation into nonempty disjoint relatively open
sets. In particular, \(S\) is not preconnected and is not connected.
This argument uses connectedness itself; it makes no assumption that a
connected subset of the plane must be path connected.

By (4), \(2i\in A\setminus M\). Hence \(A\not\subseteq M\), exactly the
straddling hypothesis in (1). Lemma 2.2 supplies \(i\in M\). All
hypotheses of (1) are therefore satisfied at \(c=i,n=16\), while its
conclusion is false. \(\square\)

## 7. Return to the categorical statement

Suppose `MLC.GreenSublevelIntersectionCategoricalData` holds. Apply it
to `Complex.I`, the membership proof \(i\in M\), and `16`.

If `greenSublevelApproximation I 16` factored through
`mandelbrotApproximation`, `factorsThrough_ofSet_iff` would give
\(A\subseteq M\), contradicting the witness \(2i\). Thus the required
non-factorisation proof is available.

The asserted `ImageConnected` conclusion, rewritten with
`image_intersection` and `image_ofSet`, is precisely
`IsConnected (A ∩ M)`. Section 6 contradicts this conclusion. Therefore

\[
\boxed{\neg\,\texttt{MLC.GreenSublevelIntersectionCategoricalData}.}
\]

Equivalently, one can apply
`MLC.greenSublevelIntersectionCategoricalData_iff` first and use the
set-theoretic contradiction from Section 6.

The existing declaration

```lean
axiom MLC.green_sublevel_intersection_categorical :
  MLC.GreenSublevelIntersectionCategoricalData
```

therefore asserts a false proposition for these definitions. Once the
mathematical soundness argument above is formalised and combined with the
checked certificate, retaining that axiom will yield `False`. An axiom
inventory that lists this declaration cannot establish its mathematical
validity.

## 8. Precise remaining work for full Lean formalisation

The target for a sound formalisation is the **negation**, not an affirmative
replacement for the current axiom. The following order avoids circular
dependencies.

1. Formalise real membership in an integer interval and complex membership
   in an interval box. Prove the rounding inequalities (8), soundness of
   the four arithmetic operations, `step`, `iterateBox`, and (9).
   These are the elementary ordered-ring and induction arguments in
   Sections 4.2–4.3.
2. Prove the interpretation of `checkCell` from Section 4.4. Keep the
   parameter orbit `orbit p 0 k` distinct from the dynamical orbit
   `orbit I (p - I) k`.
3. Prove the coverage invariant from Section 4.5, then use the nonempty
   first row to include the starting point. Apply the checked
   `certificate_checked` theorem to obtain Lemma 4.1.
4. Formalise the explicit finite invariant orbit from Lemma 2.2. Use
   `green_function_eq_zero_iff_mem_K` for the three Green-zero statements.
   Use `Molecule.mandelbrot_eq_inter` to exclude `2 * I` from \(M\).
5. Apply `Molecule.mandelbrot_subset_ball`, Lemma 4.1, and the checked
   `green_large_after_iterate` from Appendix B to obtain Lemma 5.1.
6. Apply `disconnected_of_horizontal_gap` from Appendix B, and then the
   categorical/set equivalence, to prove the negation of
   `GreenSublevelIntersectionCategoricalData`.

Suggested intermediate theorem statements are:

```lean
-- These are specifications for the remaining assembly, not claimed
-- already-compiled theorems. The complete mathematical proofs are above.

-- ∀ x ∈ [-2,2], one of two finite escape certificates applies.
∀ x : ℝ, -2 ≤ x → x ≤ 2 →
  (∃ k : ℕ, k ≤ 16 ∧
    2 < ‖MLC.Quadratic.orbit
      ((x : ℂ) + (45 / 64 : ℂ) * Complex.I) 0 k‖) ∨
  (∃ k : ℕ, k ≤ 15 ∧
    4 < ‖MLC.Quadratic.orbit Complex.I
      (((x : ℂ) + (45 / 64 : ℂ) * Complex.I) - Complex.I) k‖)

-- The separating line misses the actual intersection.
∀ p : ℂ, p ∈ MLC.Quadratic.MandelbrotSet →
  p.im = (45 / 64 : ℝ) →
  (1 / 2 : ℝ) ^ 16 <
    MLC.Quadratic.green_function Complex.I (p - Complex.I)

-- The final sound target.
¬ MLC.GreenSublevelIntersectionCategoricalData
```

The audit of existing supporting declarations reported only
`propext`, `Classical.choice`, and `Quot.sound` for:

- `MLC.greenSublevelIntersectionCategoricalData_iff`;
- `MLC.Categorical.factorsThrough_ofSet_iff`;
- `MLC.Categorical.image_intersection`;
- `Molecule.mandelbrot_eq_inter` and `Molecule.mandelbrot_subset_ball`;
- `MLC.Quadratic.green_function_eq_lim`;
- `MLC.Quadratic.green_function_eq_zero_iff_mem_K`;
- `MLC.Quadratic.green_function_iterate`;
- `MLC.Quadratic.green_function_bdd_below_log`.

In particular, none of these supporting proofs depends on
`MLC.green_sublevel_intersection_categorical` or the residual Molecule axiom.
Do not use the root MLC theorem or
`green_sublevel_translate_inter_mandelbrot_connected` as a supporting
lemma: the latter's audited dependencies include the very axiom refuted
here.

## Appendix A. Complete kernel-checked arithmetic certificate

Save the following code block verbatim as a temporary `.lean` file and run
`lake env lean /tmp/mlc_green_counterexample_certificate.lean` from this
repository. It imports only `Mathlib.Data.Int.Basic` and contains no project
axioms, `sorry`, `native_decide`, or external computation oracle. All
arithmetic uses arbitrary-precision integers. The final theorem is proved
by reduction in Lean's kernel.

The verified output is:

```text
'GreenIntersectionCertificate.certificate_checked' does not depend on any axioms
```

```lean
import Mathlib.Data.Int.Basic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace GreenIntersectionCertificate

-- An interval (lo, hi) represents [lo / scale, hi / scale].
abbrev Interval := Int × Int
abbrev Box := Interval × Interval
abbrev Cell := Int × Int × Bool × Nat

def scale : Int := 281474976710656 -- 2^48

def add (a b : Interval) : Interval := (a.1 + b.1, a.2 + b.2)
def sub (a b : Interval) : Interval := (a.1 - b.2, a.2 - b.1)
def ceilDiv (a : Int) : Int := -((-a) / scale)

def mul (a b : Interval) : Interval :=
  let v₁ := a.1 * b.1
  let v₂ := a.1 * b.2
  let v₃ := a.2 * b.1
  let v₄ := a.2 * b.2
  (min (min v₁ v₂) (min v₃ v₄) / scale,
   ceilDiv (max (max v₁ v₂) (max v₃ v₄)))

def sq (a : Interval) : Interval :=
  let lo := if a.1 ≤ 0 ∧ 0 ≤ a.2 then 0
            else min (a.1 * a.1) (a.2 * a.2)
  let hi := max (a.1 * a.1) (a.2 * a.2)
  (lo / scale, ceilDiv hi)

def step (z c : Box) : Box :=
  let xy := mul z.1 z.2
  (add (sub (sq z.1) (sq z.2)) c.1,
   add (2 * xy.1, 2 * xy.2) c.2)

def iterateBox (c : Box) : Nat → Box → Box
  | 0, z => z
  | n + 1, z => iterateBox c n (step z c)

def normLower (z : Box) : Int := (sq z.1).1 + (sq z.2).1

-- (left, right, true, k): the parameter orbit escapes past norm 2.
-- (left, right, false, k): the dynamical orbit escapes past norm 4.
-- Cell endpoints are divided by 16384, not by scale.
def cells : List Cell := [
  (-32768, -24576, false, 2),
  (-24576, -16384, false, 3),
  (-16384, -12288, false, 3),
  (-12288, -10240, false, 3),
  (-10240, -8192, false, 4),
  (-8192, -7168, false, 4),
  (-7168, -6144, false, 4),
  (-6144, -5120, false, 5),
  (-5120, -4608, false, 5),
  (-4608, -4096, false, 5),
  (-4096, -3840, false, 6),
  (-3840, -3584, false, 6),
  (-3584, -3328, false, 6),
  (-3328, -3200, false, 6),
  (-3200, -3072, false, 6),
  (-3072, -2944, false, 7),
  (-2944, -2816, false, 7),
  (-2816, -2688, false, 7),
  (-2688, -2560, false, 7),
  (-2560, -2496, false, 7),
  (-2496, -2432, false, 7),
  (-2432, -2368, false, 7),
  (-2368, -2304, false, 8),
  (-2304, -2240, false, 8),
  (-2240, -2176, false, 8),
  (-2176, -2112, false, 8),
  (-2112, -2048, false, 8),
  (-2048, -1984, false, 8),
  (-1984, -1920, false, 8),
  (-1920, -1856, false, 8),
  (-1856, -1792, false, 9),
  (-1792, -1728, false, 9),
  (-1728, -1664, false, 9),
  (-1664, -1600, false, 9),
  (-1600, -1536, false, 9),
  (-1536, -1472, false, 9),
  (-1472, -1408, false, 9),
  (-1408, -1376, false, 9),
  (-1376, -1344, false, 9),
  (-1344, -1312, false, 9),
  (-1312, -1280, false, 9),
  (-1280, -1216, false, 10),
  (-1216, -1152, false, 10),
  (-1152, -1120, false, 10),
  (-1120, -1088, false, 10),
  (-1088, -1056, false, 10),
  (-1056, -1024, false, 10),
  (-1024, -992, false, 10),
  (-992, -960, false, 10),
  (-960, -928, false, 11),
  (-928, -896, false, 11),
  (-896, -864, false, 11),
  (-864, -832, false, 11),
  (-832, -800, false, 11),
  (-800, -768, false, 11),
  (-768, -736, false, 11),
  (-736, -704, false, 11),
  (-704, -688, false, 11),
  (-688, -672, false, 11),
  (-672, -656, false, 11),
  (-656, -640, false, 11),
  (-640, -624, false, 12),
  (-624, -608, false, 12),
  (-608, -592, false, 12),
  (-592, -576, false, 12),
  (-576, -560, false, 12),
  (-560, -544, false, 12),
  (-544, -528, false, 12),
  (-528, -512, false, 12),
  (-512, -496, false, 12),
  (-496, -480, false, 12),
  (-480, -464, false, 12),
  (-464, -456, false, 12),
  (-456, -448, false, 12),
  (-448, -440, false, 12),
  (-440, -432, false, 12),
  (-432, -424, false, 12),
  (-424, -416, false, 12),
  (-416, -408, false, 13),
  (-408, -400, false, 13),
  (-400, -392, false, 13),
  (-392, -384, false, 13),
  (-384, -376, false, 13),
  (-376, -368, false, 13),
  (-368, -360, false, 13),
  (-360, -352, false, 13),
  (-352, -344, false, 13),
  (-344, -336, false, 13),
  (-336, -328, false, 13),
  (-328, -320, false, 13),
  (-320, -312, false, 13),
  (-312, -304, false, 13),
  (-304, -296, false, 13),
  (-296, -288, false, 14),
  (-288, -280, false, 14),
  (-280, -272, false, 14),
  (-272, -264, false, 14),
  (-264, -256, false, 14),
  (-256, -248, false, 14),
  (-248, -240, false, 14),
  (-240, -236, false, 14),
  (-236, -232, false, 14),
  (-232, -228, false, 14),
  (-228, -224, false, 14),
  (-224, -220, false, 14),
  (-220, -216, false, 14),
  (-216, -212, false, 14),
  (-212, -208, false, 14),
  (-208, -204, false, 14),
  (-204, -200, false, 15),
  (-200, -196, false, 15),
  (-196, -192, false, 15),
  (-192, -188, false, 15),
  (-188, -184, false, 15),
  (-184, -180, false, 15),
  (-180, -176, false, 15),
  (-176, -172, false, 15),
  (-172, -170, false, 15),
  (-170, -168, false, 15),
  (-168, -166, false, 15),
  (-166, -164, false, 15),
  (-164, -162, false, 15),
  (-162, -160, false, 15),
  (-160, -158, false, 15),
  (-158, -156, false, 15),
  (-156, -154, false, 15),
  (-154, -152, false, 15),
  (-152, -150, false, 15),
  (-150, -148, false, 15),
  (-148, -146, false, 15),
  (-146, -145, false, 15),
  (-145, -144, false, 15),
  (-144, -143, false, 15),
  (-143, -142, false, 15),
  (-142, -141, false, 15),
  (-141, -140, false, 15),
  (-140, -139, false, 15),
  (-139, -138, false, 15),
  (-138, -137, false, 15),
  (-137, -136, false, 15),
  (-136, -135, true, 16),
  (-135, -134, true, 16),
  (-134, -133, true, 16),
  (-133, -132, true, 16),
  (-132, -131, true, 16),
  (-131, -130, true, 16),
  (-130, -129, true, 16),
  (-129, -128, true, 16),
  (-128, -127, true, 15),
  (-127, -126, true, 15),
  (-126, -125, true, 15),
  (-125, -124, true, 15),
  (-124, -123, true, 15),
  (-123, -122, true, 15),
  (-122, -121, true, 15),
  (-121, -120, true, 15),
  (-120, -119, true, 15),
  (-119, -118, true, 15),
  (-118, -117, true, 15),
  (-117, -116, true, 15),
  (-116, -115, true, 15),
  (-115, -114, true, 15),
  (-114, -112, true, 15),
  (-112, -110, true, 15),
  (-110, -108, true, 15),
  (-108, -106, true, 15),
  (-106, -104, true, 15),
  (-104, -102, true, 15),
  (-102, -100, true, 15),
  (-100, -98, true, 15),
  (-98, -96, true, 15),
  (-96, -94, true, 15),
  (-94, -92, true, 15),
  (-92, -90, true, 14),
  (-90, -88, true, 14),
  (-88, -86, true, 14),
  (-86, -84, true, 14),
  (-84, -82, true, 14),
  (-82, -80, true, 14),
  (-80, -78, true, 14),
  (-78, -76, true, 14),
  (-76, -74, true, 14),
  (-74, -72, true, 14),
  (-72, -68, true, 14),
  (-68, -64, true, 14),
  (-64, -60, true, 14),
  (-60, -56, true, 14),
  (-56, -52, true, 14),
  (-52, -48, true, 14),
  (-48, -44, true, 14),
  (-44, -40, true, 14),
  (-40, -36, true, 13),
  (-36, -32, true, 13),
  (-32, -28, true, 13),
  (-28, -24, true, 13),
  (-24, -20, true, 13),
  (-20, -16, true, 13),
  (-16, -12, true, 13),
  (-12, -8, true, 13),
  (-8, -4, true, 13),
  (-4, 0, true, 13),
  (0, 8, true, 13),
  (8, 16, true, 13),
  (16, 24, true, 13),
  (24, 32, true, 13),
  (32, 40, true, 13),
  (40, 48, true, 13),
  (48, 56, true, 13),
  (56, 64, true, 13),
  (64, 72, true, 13),
  (72, 80, true, 12),
  (80, 88, true, 12),
  (88, 96, true, 12),
  (96, 104, true, 12),
  (104, 112, true, 12),
  (112, 128, true, 12),
  (128, 144, true, 12),
  (144, 160, true, 12),
  (160, 176, true, 12),
  (176, 192, true, 12),
  (192, 208, true, 12),
  (208, 224, true, 12),
  (224, 240, true, 11),
  (240, 256, true, 11),
  (256, 272, true, 11),
  (272, 288, true, 11),
  (288, 304, true, 11),
  (304, 320, true, 11),
  (320, 336, true, 11),
  (336, 352, true, 11),
  (352, 384, true, 11),
  (384, 416, true, 11),
  (416, 448, true, 11),
  (448, 480, true, 11),
  (480, 512, true, 11),
  (512, 576, true, 11),
  (576, 640, true, 11),
  (640, 704, true, 11),
  (704, 736, true, 10),
  (736, 768, true, 10),
  (768, 832, true, 10),
  (832, 896, true, 10),
  (896, 960, true, 10),
  (960, 1024, true, 9),
  (1024, 1088, true, 9),
  (1088, 1152, true, 9),
  (1152, 1216, true, 9),
  (1216, 1280, true, 9),
  (1280, 1344, true, 9),
  (1344, 1408, true, 9),
  (1408, 1472, true, 9),
  (1472, 1536, true, 9),
  (1536, 1600, true, 9),
  (1600, 1664, true, 9),
  (1664, 1728, true, 9),
  (1728, 1792, true, 9),
  (1792, 1856, true, 9),
  (1856, 1920, true, 9),
  (1920, 1984, true, 9),
  (1984, 2016, true, 9),
  (2016, 2048, true, 9),
  (2048, 2112, false, 11),
  (2112, 2176, false, 10),
  (2176, 2240, false, 10),
  (2240, 2272, true, 8),
  (2272, 2304, true, 8),
  (2304, 2336, true, 8),
  (2336, 2368, true, 8),
  (2368, 2432, true, 8),
  (2432, 2496, true, 8),
  (2496, 2560, true, 8),
  (2560, 2624, true, 8),
  (2624, 2688, true, 7),
  (2688, 2752, true, 7),
  (2752, 2816, true, 7),
  (2816, 2944, true, 7),
  (2944, 3072, true, 7),
  (3072, 3200, true, 7),
  (3200, 3328, true, 7),
  (3328, 3456, true, 7),
  (3456, 3584, true, 7),
  (3584, 3712, true, 6),
  (3712, 3840, true, 6),
  (3840, 4096, true, 7),
  (4096, 4352, true, 7),
  (4352, 4608, false, 7),
  (4608, 4864, true, 7),
  (4864, 5120, true, 7),
  (5120, 5632, false, 7),
  (5632, 6144, false, 6),
  (6144, 6656, false, 6),
  (6656, 7168, false, 6),
  (7168, 7680, true, 6),
  (7680, 8192, true, 4),
  (8192, 10240, true, 4),
  (10240, 12288, true, 3),
  (12288, 16384, true, 3),
  (16384, 32768, true, 2)
]

def checkCell (t : Cell) : Bool :=
  let (a, b, parameter, k) := t
  let x : Interval := (a * (scale / 16384), b * (scale / 16384))
  let y : Int := 45 * (scale / 64)
  let p : Box := (x, (y, y))
  let result := if parameter
    then iterateBox p k ((0, 0), (0, 0))
    else iterateBox ((0, 0), (scale, scale)) k (x, (y - scale, y - scale))
  decide (a < b ∧ 1 ≤ k ∧
    (if parameter then k ≤ 16 else k ≤ 15) ∧
    normLower result > (if parameter then 4 else 16) * scale)

def coverFrom : Int → List Cell → Bool
  | a, [] => decide (a = 32768)
  | a, (l, r, _, _) :: tail => decide (a = l ∧ l < r) && coverFrom r tail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem certificate_checked :
    coverFrom (-32768) cells = true ∧ cells.all checkCell = true := by
  decide

#print axioms certificate_checked

end GreenIntersectionCertificate
```

## Appendix B. Checked analytic and topological helper proofs

This second code block is a separate Lean file. Its two theorems compile
against the repository as inspected. Each reports only `propext`,
`Classical.choice`, and `Quot.sound`; neither uses the target axiom.

```lean
import Mlc.ParaPuzzleConnectivity

open Complex Set MLC.Quadratic

namespace GreenIntersectionCounterexample

theorem disconnected_of_horizontal_gap {S : Set ℂ}
    (h0 : (0 : ℂ) ∈ S) (hi : Complex.I ∈ S)
    (hgap : ∀ z ∈ S, z.im ≠ (45 / 64 : ℝ)) :
    ¬ IsConnected S := by
  intro hS
  have hm : (45 / 64 : ℝ) ∈ Set.Icc ((0 : ℂ).im) Complex.I.im := by
    norm_num
  obtain ⟨z, hz, heq⟩ := hS.isPreconnected.intermediate_value
    h0 hi Complex.continuous_im.continuousOn hm
  exact hgap z hz heq

theorem green_large_after_iterate {z : ℂ} {k : ℕ} (hk : k ≤ 15)
    (hesc : 4 < ‖orbit Complex.I z k‖) :
    (1 / 2 : ℝ) ^ 16 < green_function Complex.I z := by
  let w := orbit Complex.I z k
  have hbound : escape_bound Complex.I = 2 := by
    rw [escape_bound_eq_max]
    norm_num
  have hw : escape_bound Complex.I < ‖w‖ := by
    rw [hbound]
    dsimp [w]
    linarith
  have hlow := green_function_bdd_below_log Complex.I w hw
  rw [hbound] at hlow
  norm_num at hlow
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlogw : Real.log 4 < Real.log ‖w‖ :=
    Real.log_lt_log (by norm_num) hesc
  have hgreenw : (1 / 2 : ℝ) < green_function Complex.I w := by
    linarith
  have hiterate := green_function_iterate Complex.I z k
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ 15 :=
    pow_le_pow_right₀ (by norm_num) hk
  by_contra! hnot
  have hupper : (2 : ℝ) ^ k * green_function Complex.I z ≤ (1 / 2 : ℝ) := by
    calc
      (2 : ℝ) ^ k * green_function Complex.I z ≤
          (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ 16 := by gcongr
      _ ≤ (2 : ℝ) ^ 15 * (1 / 2 : ℝ) ^ 16 := by gcongr
      _ = (1 / 2 : ℝ) := by norm_num
  dsimp [w] at hgreenw
  rw [hiterate] at hgreenw
  exact (not_lt_of_ge hupper) hgreenw

#print axioms disconnected_of_horizontal_gap
#print axioms green_large_after_iterate

end GreenIntersectionCounterexample
```

## Appendix C. Double-check record

The review checked the following distinct obligations.

| Obligation | Evidence |
| --- | --- |
| Exact target, not a similarly named parapuzzle theorem | Unfolded the actual categorical definitions and checked their set-theoretic equivalence. |
| Correct Green normalisation and translation | Used the repository's limit with factor \(2^{-m}\), starting point \(p-i\), and level \((1/2)^{16}\). |
| Base parameter in \(M\) | Explicit eventually periodic critical orbit of \(i\). |
| Nonempty pieces on both sides | Explicit bounded dynamical orbits give \(0,i\in A\cap M\). |
| Non-factorisation hypothesis | Explicit witness \(2i\in A\setminus M\). |
| Every real point on the potential separating line | Adjacent closed interval coverage of \([-2,2]\), kernel-checked, combined with \(|\operatorname{Re}p|\le2\) for \(p\in M\). |
| Correct direction of every finite orbit inference | Only strict finite escape is used, never finite non-escape as proof of boundedness. |
| Exact arithmetic, including endpoints | All 298 rows verified in Lean with integer outward rounding and strict squared-norm bounds. |
| Independent implementation | All 298 rows rechecked using Python `Fraction` arithmetic with outward rounding to scale \(2^{80}\), independently of the Lean integer implementation at scale \(2^{48}\). |
| Depth and factor-of-two accounting | Dynamical rows have \(k\le15\); \(G_i(F_i^k(z))>1/2\) gives \(G_i(z)>2^{-(k+1)}\ge2^{-16}\). |
| Actual disconnectedness | Explicit separation by relatively open half-planes; independently checked Lean intermediate-value argument. |
| No circular use of the axiom | Arithmetic proof has no axioms; existing analytic/category helpers and the checked Appendix B proofs have only standard Lean foundations. |

The independent rational recheck reported:

```text
Independent rational recheck passed: {'G': 148, 'M': 150}
at 80-bit outward precision; no floating point used.
```

The full Lean formalisation must still connect the interval semantics to the
arithmetic certificate as described in Section 8. The complete mathematical
argument and all its finite arithmetic data are present in this file.
