# B3: targeted publication-novelty screening

**Status on 8 November 2026:** the Pilgrim direction, in the separate
`pilgrim-bisets` package. The main B3 theorem is unproved; no implication
to MLC is established. The mathematical audit of 7 November is preserved below.

7 November 2026. Literature and public-computation screening.

**Decision: the full B3 theorem passes literature screening as a proposed
paper result.** The proposed contribution is a finite global attractor
for the five-postcritical-point rabbit–Basilica mating, with an explicit
class list and global-attraction certificate.
No such result was found in the works checked below, and the checked
general theorems do not supply it.

This is the outcome of literature comparison as of the stated date.
The main theorem remains unproved. Selection does not predict journal acceptance.

**Continuation condition:** B3 work must produce a proof for an arbitrary
curve. A biset recursion, finite search, invariant tree, known equator,
or obstruction to strong contraction alone is not the publication goal.

## 1. Three separately screened claims

Let
$$
F(z)=\frac{z^2+\lambda}{z^2-1},\qquad
\lambda=\frac{1+i\sqrt3}{2},\qquad
P=\{0,-\lambda,1-\lambda,\infty,1\}.
$$
Curve notation and $\mathcal P_F$ are defined in the [B3 statement](B3_candidate.md).

1. **B3-E: existence.** A finite set $\mathcal A$ is invariant under
   $\mathcal P_F$, and
   $$
   \forall\gamma\in\mathcal C(S^2,P)\ \exists N(\gamma)\
   \forall n\ge N(\gamma):\quad
   \mathcal P_F^{\,n}(\gamma)\subseteq\mathcal A.
   $$
   This is the main substantive claim.
2. **B3-A: explicit description.** Coordinates of $\mathcal A$, every
   internal transition, and a checkable certificate of B3-E are supplied.
   The explicit list must accompany a general proof.
3. **B3-M: method.** An additional general curve- or twist-control lemma.
   No such new lemma has been formulated. A methodological generalization
   is not claimed in advance as the paper's contribution.

B3 is selected on B3-E together with B3-A. Screening the statement's
novelty does not require its proof in advance; obtaining the result
will require proving that statement.

## 2. Identifying the map and equivalent forms

### Translation to the critical-two-cycle family

Let $T(z)=z-1$ and $a=1+\lambda=(3+i\sqrt3)/2$. Then
$$
T\circ F\circ T^{-1}(w)
=F(w+1)-1
=\frac{1+\lambda}{(w+1)^2-1}
=\frac{a}{w^2+2w}=:R_a(w).
\tag{P1}
$$
The rational-function identity extends over the sphere. Also,
$$
a^2-3a+3=0,
$$
$$
\infty\mapsto0\mapsto\infty,\qquad
-1\mapsto-a\mapsto-\lambda\mapsto-1.
$$
Another form: for $\omega=e^{2\pi i/3}$, $\lambda=-\omega^2$, so
$$
F(z)=\frac{z^2-\omega^2}{z^2-1}.
\tag{P2}
$$
Form (P2) appears in Buff–Epstein–Koch,
[*Twisted matings and equipotential gluings*](https://www.numdam.org/item/AFST_2012_6_21_S5_995_0.pdf),
Figure 2, printed p. 1004. That paper's main developed example is a
twisted self-mating of the Basilica; §§1.3.3–1.3.4 identify our map
as a geometric mating. They do not prove its global attractor for all curves.

### The critical scheme determines two conjugate parameters

The following elementary classification helps check other names for the
example. Suppose a quadratic rational map has two disjoint critical
cycles of exact periods $2$ and $3$. Normalize the critical point in
the two-cycle to $\infty$, its image to $0$, and the other critical
point to $-1$.

Criticality at $\infty$ and $R(\infty)=0$ force a nonzero constant
numerator. The condition $R(0)=\infty$ forces zero constant denominator
term. Normalizing its leading coefficient gives $a/(w^2+bw)$.
The other critical point is $-b/2$, so $b=2$.
The remaining family is (P1), with $a\ne0$.

For $a\notin\{0,2,3/2\}$, direct calculation gives
$$
R_a(-1)=-a,\qquad
R_a^2(-1)=\frac1{a-2},\qquad
R_a^3(-1)+1=\frac{(a-1)(a^2-3a+3)}{2a-3}.
\tag{P3}
$$
The parameter $a=0$ is degenerate; at $a=2$ or $3/2$, $-1$ enters
the two-cycle through a pole and has no period $3$.
At $a=1$ it is fixed. Hence the required parameters are exactly
$(3\pm i\sqrt3)/2$. Their three-cycles consist of three distinct,
finite, nonzero points and avoid $\{0,\infty\}$.

The scheme therefore reduces the search to our map and its complex conjugate.
Complex reflection carries curves and pullbacks between them, so they
have the same finite-global-attractor property.
This classification identifies the object; it does not extend B3 to
a parameter family.

## 3. Comparison with the nearest theorems

For exclusions proved in the first audit, use the
[complete arguments](B3_novelty_audit.md) and
[all-iterate bounds](B3_candidate.md), §3.

| Source | Applicability to B3 |
| --- | --- |
| BDP; BHL; Smith | Four points required |
| BLMW; Wang–Zhang | Polynomial required |
| Hlushchanka–Prochorov | Critically fixed case |
| Wu | Excluded by local degrees |
| Pilgrim; KPS 7.2(1) | Required contraction excluded |
| KPS 7.2(2) | Equator excludes the hypothesis |
| Parry–Pilgrim | Biset contains an obstructed element |
| Shepelevtseva–Timorin | Known invariant tree |

Exact hypotheses, theorem numbers, and conclusions follow.

### Four marked points

- Bartholdi–Dudko–Pilgrim,
  [2025v2](https://arxiv.org/abs/2407.15548v2), Corollary B, §§1.1, 1.3:
  finite curve and graph attractors for four postcritical points.
  Our $F$ and every iterate have five. The higher-dimensional discussion
  in §1.3 gives a research strategy, not a ready B3 theorem.
- Bonk–Hlushchanka–Lodge,
  [2024v1](https://arxiv.org/abs/2411.00732v1), Theorems 1–2,
  Corollary 6, §4.3: $|P|=4$ is required. Our map satisfies periodicity
  of marked critical points but violates the point count. These theorems
  provide no general $|P|=5$ version.
- Smith,
  [2024v1](https://arxiv.org/abs/2401.16636v1), Theorems 1.2–1.3:
  four marked points, at most three postcritical points, or a special
  static reducibility condition with four postcritical points.
  Section 6 discusses a possible continuation, without asserting B3-E.
- Lodge,
  [2013 paper, preprint v1](https://arxiv.org/abs/1212.2672v1), §§3–7,
  and [2012 thesis](https://mathcs.indstate.edu/~rlodge/LodgeThesisFinal1.pdf),
  §§3–8: a general algorithm in the four-point setting and a developed
  cubic example $3z^2/(2z^3+1)$. Its degree and four postcritical points
  differ from B3, so that result does not transfer.

### Polynomials, critically fixed maps, and gluings

- Belk–Lanier–Margalit–Winarski,
  [preprint](https://arxiv.org/abs/1906.07680), Theorem 1.1 and Corollary 1.2:
  tree pullback and a finite attractor for polynomials.
  An invariant tree alone does not replace the polynomial hypothesis.
- Wang–Zhang,
  [2026v4](https://arxiv.org/abs/2601.04871v4), Main Theorem:
  an exponential curve-complexity bound for PCF polynomials.
  Neither $F$ nor its iterates are conjugate to a polynomial.
- Hlushchanka–Prochorov,
  [2026v2](https://arxiv.org/abs/2212.14759v2), Main Theorem B:
  a global admissible-tree attractor for critically fixed maps.
  No $F^n$, $n\ge1$, is critically fixed.
- Wu,
  [2026v2](https://arxiv.org/abs/2605.00633v2), Main Theorem, §§1.1, 2.2–2.3:
  gluing two polynomials along finite basins. The distinction from mating
  along external rays matters. Incompatibility of the required local
  degrees was proved for every iterate of $F$.
  The paper's intersection control is relevant to the method, but its
  Main Theorem does not apply to B3.

### Criteria on moduli space

Koch–Pilgrim–Selinger,
[*Pullback invariants of Thurston maps*](https://arxiv.org/abs/1212.4568v1),
Theorem 7.2, gives two further general criteria.
The existing data exclude both for B3.

1. **A nonempty compact invariant set of the correspondence.**
   Theorem 7.2(1) implies $\rho(\varphi_F)<1$.
   The first audit proves $\rho(\varphi_F)\ge1$, so the hypothesis is false.
2. **Uniform contraction in a WP-like metric.**
   Theorem 7.2(2) implies eventual triviality of every essential curve.
   The known equator satisfies
   $\gamma_{\rm eq}\in\mathcal P_F^n(\gamma_{\rm eq})$ for every $n$,
   so this hypothesis is false too.

Theorems 9.1–9.2 of the same work already relate obstructed twists,
surjectivity, and long chains in the four-point case.
Our auxiliary calculations are not claimed as a new general mechanism.

Parry–Pilgrim,
[2025v1](https://arxiv.org/abs/2506.23222v1), Theorems 1.1–1.2:
contraction concerns the whole Hurwitz biset. The obstructed map in the
same pure class, constructed in the first audit, excludes that contraction.
The five-point example in §8.2 is a polynomial of another degree.

## 4. Invariant trees and subsequent work

Shepelevtseva–Timorin,
[2021v4](https://arxiv.org/abs/1808.05489v4), §2.2, Theorem 5.6, §§7.1–7.5:
an invariant tree for the formal rabbit–Basilica mating, and its biset
construction. Computed finite invariant ivy-graph subsets describe
particular trees. No proof is given that every curve for our map enters
a finite list. The questions in §7.5 reflect that paper's date and are
not evidence of openness in 2026.

To find later work, the OpenAlex citation results for DOI
`10.1007/s40598-019-00123-w` were checked through 7 November 2026.
They returned six works. Metadata guided the search;
mathematical conclusions were checked against primary sources:

1. Belk–Lanier–Margalit–Winarski: the polynomial case, discussed above.
2. Cui–Gao–Zeng,
   [*Invariant graphs of rational maps*, 2022v2](https://arxiv.org/abs/1907.02870v2),
   Theorem 1.1 and introduction: existence of a finite invariant graph for
   a sufficiently large iterate of a PCF map. Attraction of every curve
   to a finite list is not a conclusion of that theorem.
3. Mukundan–Winarski,
   [*A solution to the degree-d twisted rabbit problem*](https://arxiv.org/abs/2209.06099v1),
   Theorem 1.1: twists of degree-$d$ polynomials, a different object.
4. Park,
   [*Levy and Thurston obstructions of finite subdivision rules*, v4](https://arxiv.org/abs/2012.00243v4),
   Theorems 6.21, 8.6, Corollary 7.10: obstruction detection and rational
   realization criteria, including zero-core-entropy matings.
   Our map's rational realization is known; B3-E needs an additional
   statement about the dynamics of every curve.
5. Yetişer–Yetişer,
   [*On elastic graph spines associated to quadratic Thurston maps*](https://journals.tubitak.gov.tr/math/vol46/iss4/7/),
   publisher abstract: portrait counts, elastic spines for several
   four-point examples, and rational realization. B3-E is absent from
   these stated results; the full text was not included in the proof audit.
6. Hlushchanka–Prochorov: the critically fixed case, discussed above.

Six is the count in that database result alone; no complete bibliography
is claimed. Additional references came from
[Pilgrim, §4.1](https://arxiv.org/abs/2102.12402v1), the Wu and Wang–Zhang
introductions, and a separate search for forms (P1)–(P2).

Shota Kohara's thesis on
[canonical obstructions for formal matings](https://www.cajpn.org/refs/thesis/19M-Kohara.pdf)
was checked through its English abstract and contents.
It concerns numerical study of obstructed matings by Jung's method
and limiting rational maps. No proof of B3-E for our unobstructed mating
was found in the inspected parts.

## 5. Audit of public computations

[Pf4Source.zip, release 2.0](https://sourceforge.net/projects/pf4/files/2.0/Pf4Source.zip/download)
was downloaded and its ZIP integrity checked. The input model,
marked-point structures, input validation, and scrambler-related sections
were inspected.

- `Pf4Release2/runpf4.cpp`, lines 132–190, 242–260, and 1919 onward:
  four labels, marked-point index arrays $1,2,3,4$,
  and input of exactly four marked points.
- `Pf4Release2/draw.cpp`, lines 3219–3238:
  validation requiring exactly four marked points.
- [ChangesInPf4_2.pdf](https://sourceforge.net/projects/pf4/files/2.0/ChangesInPf4_2.pdf/download),
  p. 2: the scrambler and further Hurwitz-biset information.

This release does not accept B3's five-point marking.
Static inspection found no ready B3 attractor.
The program was neither compiled nor executed.

Parry–Pilgrim §1.3 mentions implementations for four and five points.
No separate five-point package was identified through the public links;
this search limitation is recorded explicitly. However, the output
specified there, a strata scrambler for the entire Hurwitz biset,
does not itself prove B3-E: strong contraction is already excluded
for our biset. Mention of software is not a known solution to B3-E.

The targeted check also found
[Chéritat's visualization](https://www.math.univ-toulouse.fr/~cheritat/MatMovies/RabbitBasilica/).
It illustrates mating and slow mating. A numerical Julia-set image
is not a certificate of attraction for every curve isotopy class.

Checksums of downloaded material and citation records are in the
[audit manifest](B3_publication_evidence.json).
Third-party programs and articles are not included in the commit.

## 6. Contribution assessment and programme decision

**Supported paper goal:** prove B3-E and supply B3-A for the fixed map (P1).
This tests the general finite-global-attractor conjecture in a concrete
five-point nonpolynomial case outside the checked theorems.
The substantive difficulty is controlling infinitely many isotopy
classes without strong mapping-class contraction.

The comparison supports novelty of this full goal specifically.
The known tree and equator are already accounted for as input data.
An additional general lemma or quantitative bound could strengthen the
paper once obtained; neither is attributed to B3 in advance to justify selection.

Criteria for the work's outcome:

1. **Paper result:** an argument for every curve proving B3-E, together
   with a reproducible description B3-A.
2. **Revise the goal:** a ready proof of B3-E or a short reduction to a
   known theorem is found. Reassess the independent value of B3-A;
   a curve list alone is not assumed to support a paper.
3. **Insufficient paper result:** only a recursion, finite experimental
   graph, one-family formula, or first-audit lemmas are obtained.
   Retain those data, but do not mark the first-paper goal complete.

Literature screening gave no basis to close B3 as a known consequence.
**The full theorem is admitted as a publication problem;
its proof remains the main unfinished work.**