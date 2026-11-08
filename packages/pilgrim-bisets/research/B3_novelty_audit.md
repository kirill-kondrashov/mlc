# B3: detailed audit results

**Status on 8 November 2026:** the Pilgrim direction, in the separate
`pilgrim-bisets` package. The main B3 theorem is unproved; no implication
to MLC is established. The mathematical audit of 7 November is preserved below.

**Addendum:** the later [targeted publication-novelty screening](B3_publication_screening.md)
supports novelty of the full B3 theorem. The obstruction proofs and limits
of the first feasibility check are preserved below.

7 November 2026. We audit the explicit finite global curve attractor for

$$
F(z)=\frac{z^2+\lambda}{z^2-1},\qquad
\lambda=\frac{1+i\sqrt3}{2},\qquad
P=\{0,-\lambda,1-\lambda,\infty,1\}.
$$

**No reduction closing B3 as a known consequence has been found.**
However, the Pilgrim criterion left open in the initial card is now checked:
**its contraction hypothesis fails for this map**.
A complete proof follows. The main attractor theorem is still neither
proved nor disproved.

This differs from B2-N, where every proposed invariant was computed.
For B3, the following auxiliary statements are proved:

1. Every curve has at most one essential pullback component;
   the pullback relation is a partial function.
2. The moduli correspondence is computed, and the mapping-class virtual
   endomorphism is surjective.
3. A map in the Hurwitz class of $F$ with a fixed Levy curve is constructed.
4. For $F$ itself, arbitrarily long degree-one pullback chains preserve
   the same puncture partition.
5. The contraction coefficient of $\varphi_F$ is at least $1$.
   A height depending only on puncture partitions cannot yield the
   proposed certificate, even after a fixed number of steps.

**Decision:** retain B3 as a concrete research conjecture.
The additional step is control of isotopy classes and twists for the
fixed rational map $F$. A graph of puncture partitions and the strong
contraction criterion do not solve this. The audit's auxiliary statements
are not claimed as an independent new paper result.

# 1. Literature comparison

The main additional source is Parry–Pilgrim,
[*Characterizations of contracting Hurwitz bisets*, 2025v1](https://arxiv.org/abs/2506.23222v1).
Theorems 1.1–1.2, definitions in §§2–4, and correspondence models in
§§6.5–6.6 were checked. Their contraction concerns the whole Hurwitz biset.
By Theorem 1.2, it implies unobstructedness of every element in the
generated semigroup family. The obstructed element constructed below
rules out this contraction hypothesis.

Pilgrim,
[*An algebraic formulation of Thurston's characterization of rational functions*](https://www.numdam.org/article/AFST_2012_6_21_S5_1033_0.pdf),
Theorem 1.4, printed p. 1039, and §7, pp. 1052–1055:
a contracting virtual endomorphism gives a finite attractor.
Below we prove $\rho(\varphi_F)\ge1$ directly.

Bartholdi–Dudko–Pilgrim,
[*Correspondences on Riemann surfaces and non-uniform hyperbolicity*, 2025v2](https://arxiv.org/abs/2407.15548v2),
Corollary B assumes four postcritical points.
The discussion in §§1.1, 5.1 distinguishes strong contraction of the
whole biset from weaker control along one map. This matters:
failure of Hurwitz-biset contraction does not disprove an attractor for $F$.

The comparison with Wu's 2026v2 gluing theorem was rechecked:
the [local-degree argument](B3_candidate.md), §3, excludes that theorem
for every iterate of $F$. Polynomial and critically fixed theorems
remain inapplicable as well.

The known map and equator in
[Bonnot–Braverman–Yampolsky, 2010v1](https://arxiv.org/abs/1009.5713v1),
§2, pp. 3–4, remain a calibration. Neither this equator nor its multiplier
$1/2$ gives a statement about all curves.
An ivy-iteration source was also checked:
[Shepelevtseva–Timorin, 2021v4](https://arxiv.org/abs/1808.05489v4),
§2.2 gives an invariant tree of the formal rabbit–Basilica mating;
Theorem 5.6 constructs the biset from the tree. These supply an initial
computational model, not global attraction of all curves.

# 2. Notation and exact audit target

Label the points

$$
a_0=0,\quad a_1=-\lambda,\quad a_2=1-\lambda,\qquad
b_0=\infty,\quad b_1=1.
$$

Then $F(a_i)=a_{i+1\bmod3}$, $F(b_j)=b_{j+1\bmod2}$.
The critical points are $a_0,b_0$, and the critical values are $a_1,b_1$.
Both local degrees are $2$, and $F|_P$ is a permutation.

Let $\mathcal C$ consist of isotopy classes of unoriented essential
simple closed curves in $S^2-P$. Each class separates the punctures
into sides of sizes $2$ and $3$.
Let $\mathcal P_F(\gamma)$ be the set of essential pullback-component
classes. B3 asserts

$$
\exists\ \text{an explicit finite }\mathcal A\subset\mathcal C:
\quad \mathcal P_F(\mathcal A)\subseteq\mathcal A,
$$
$$
\forall\gamma\in\mathcal C\ \exists N\
\forall n\ge N:\quad \mathcal P_F^{\,n}(\gamma)\subseteq\mathcal A.
\tag{A1}
$$

The time $N$ depends on $\gamma$. This does not require a common
entry bound for all initial curves.

Two different groups are needed:

- $\pi_1(S^2-P)\simeq F_4$, the group of the dynamical biset.
- $\mathcal G=\operatorname{PMod}(S^2,P)\simeq\pi_1(\mathcal M_{0,5})$,
  the pure mapping class group carrying $\varphi_F$.

Contraction of one construction is not identified with contraction of the other.

# 3. Uniqueness of the essential pullback component

**Lemma.** For every $\gamma\in\mathcal C$,
$\#\mathcal P_F(\gamma)\le1$. If a component exists, its degree is $1$ or $2$.

**Proof.** Choose a representative, and let $D$ be its complementary
topological disk containing exactly two points of $P$.
Let $r$ be the number of critical values in $D$.

Since $F|_P$ is bijective,
$$
\#(F^{-1}(D)\cap P)=\#(D\cap P)=2.
\tag{A2}
$$
The remaining counts concern only marked points of $P$.

If $r=0$, $F^{-1}(D)$ consists of two disks, each mapping to $D$
with degree $1$. Their marked-point distributions are $2+0$, $1+1$,
or $0+2$. Exactly one boundary is essential in the first and third
cases, and none in the second.

If $r=1$, the preimage is a single degree-$2$ disk.
Its unique boundary is essential by (A2), with three marked points
on the other side. Boundary monodromy is a transposition, also giving
this preimage description.

If $r=2$, the preimage of $D$ is an annulus with two degree-one boundary
components. For example, Riemann–Hurwitz gives Euler characteristic
$2-2=0$, with trivial boundary monodromy.
Exactly two marked points lie in the annulus. The remaining three lie
in its two complementary disks, distributed as $3+0$, $2+1$, $1+2$,
or $0+3$. Exactly one complementary disk has at least two marked points,
so exactly one boundary is essential. These exhaust the cases. $\square$

Thus B3 can be studied here as orbits of a partial function.
An orbit terminates when no essential pullback exists.

# 4. The moduli correspondence

Normalize the target's five marked points as
$$
(a_0,a_1,a_2,b_0,b_1)=(0,x,y,\infty,1).
$$
Then
$$
\mathcal M=\{(x,y)\in\mathbb C^2:
x,y\notin\{0,1\},\ x\ne y\}
\simeq\mathcal M_{0,5}.
$$

On the source sphere use $(0,s,t,\infty,1)$.
A quadratic covering with critical points $0,\infty$ and
$R(\infty)=1$, $R(1)=\infty$, $R(0)=x$ must have the form
$$
R_x(z)=\frac{z^2-x}{z^2-1}.
$$
This is the usual normal form: after normalizing critical points,
a quadratic covering is a Möbius function of $z^2$.
Equivalently, its nontrivial deck transformation fixes $0,\infty$
and is $z\mapsto-z$.

The remaining marked-image conditions $R_x(t)=0$, $R_x(s)=y$ give
$$
x=t^2,\qquad y=\frac{s^2-t^2}{s^2-1}.
$$
Thus the Hurwitz-class correspondence is
$$
\phi,\rho:\mathcal U\rightrightarrows\mathcal M,\qquad
\phi(s,t)=\left(t^2,\frac{s^2-t^2}{s^2-1}\right),\quad
\rho(s,t)=(s,t),
\tag{A3}
$$
$$
\mathcal U=\{(s,t)\in\mathbb C^2:
s,t\notin\{0,1,-1\},\ s\ne t,\ s\ne-t\}.
$$

**Lemma.** $\phi$ is a connected unbranched degree-$4$ covering;
$\rho$ is an inclusion surjective on fundamental groups.

**Proof.** Over each $(x,y)\in\mathcal M$, there are exactly four pairs
$$
t=\pm\sqrt{x},\qquad s=\pm\sqrt{\frac{y-x}{y-1}}.
$$
Neither radicand is $0$ or $1$, and $s^2\ne t^2$ since $y(1-x)\ne0$.
Hence all pairs belong to $\mathcal U$.
Local square-root choices give four local inverse branches.

The set $\mathcal U$ is the complement of eight complex lines.
It is connected: the complex line through any two of its points lies
in none of the excluded lines and loses only finitely many points;
what remains is path-connected.

Moreover,
$$
\mathcal U=\mathcal M-\{s=-1\text{ or }t=-1\text{ or }s+t=0\}.
$$
Any loop in $\mathcal M$ can be perturbed slightly relative to its
basepoint to avoid these complex divisors, of real codimension $2$.
The perturbation gives a homotopic loop in $\mathcal U$.
Thus $\rho_*$ is surjective. $\square$

Put $p=(-\lambda,1-\lambda)$. Substituting $\lambda^2=\lambda-1$
gives $\phi(p)=\rho(p)=p$. This fixed point corresponds to the original
rational map $F=R_{-\lambda}$.
Under the usual identification with the moduli fundamental group,
$$
H=\phi_*\pi_1(\mathcal U,p)\le\mathcal G,\qquad
[\mathcal G:H]=4,\qquad
\varphi_F=\rho_*\circ(\phi_*)^{-1}:H\longrightarrow\mathcal G.
\tag{A4}
$$
This is the standard lift-and-forget model; Parry–Pilgrim, §§6.5–6.6,
compare map and path bisets. The opposite multiplication convention
uses opposite groups, leaving surjectivity and the contraction coefficient unchanged.

**In particular, $\varphi_F$ is surjective.**
The degree $4$ in (A4) concerns the mapping-class biset;
the dynamical biset over $F_4$ has degree $2$.

# 5. An obstructed element of the same Hurwitz class

This step tests strong contraction. It does not assert a Levy curve
for the rational map $F$.

Choose rational parameters
$$
s_*=\frac{101}{100},\quad t_*=-\frac{99}{100},\quad
x_*=t_*^2=\frac{9801}{10000},\quad
y_*=\frac{s_*^2-t_*^2}{s_*^2-1}=\frac{400}{201}.
\tag{A5}
$$
View $R_{x_*}$ as a covering **between two different marked spheres**:
$$
(0,s_*,t_*,\infty,1)\longrightarrow(0,x_*,y_*,\infty,1).
$$
It has exactly the same label dynamics $a_i,b_j$ as $F$.
No interpretation of $R_{x_*}$ as a PCF rational self-map is required here.

Let $\gamma_*$ be $|w-1|=1/4$.
Exactly the two target marks $x_*,1$ lie inside:
$1-x_*=199/10000<1/4$, whereas $y_*-1=199/201>1/4$,
and $0,\infty$ are outside. Let $E$ be the exterior closed disk, including $\infty$.

From
$$
R_{x_*}(z)-1=\frac{1-x_*}{z^2-1}
$$
we obtain
$$
R_{x_*}^{-1}(E)=
\left\{z:\ |z^2-1|\le\frac{199}{2500}\right\}.
\tag{A6}
$$
Since $199/2500<1$, these are two disks $D_+,D_-$ around $1,-1$.
The map $z^2$ maps each bijectively onto
$\{|u-1|\le199/2500\}$; hence $R_{x_*}:D_\pm\to E$ also has degree $1$.

Exactly the source marks $1,s_*$ lie in $D_+$:
$$
|s_*^2-1|=\frac{201}{10000}<\frac{199}{2500}.
$$
The point $t_*$ lies in $D_-$, since
$$
|t_*^2-1|=\frac{199}{10000}<\frac{199}{2500}.
$$
Neither $0$ nor $\infty$ belongs to these disks.
Thus $\alpha_*=\partial D_+$ is essential and separates the same labels
$\{a_1,b_1\}$ as $\gamma_*$. The other component $\partial D_-$ is peripheral.

Fix any curve $\Gamma$ on the original marked sphere separating
$\{a_1,b_1\}$. Choose orientation-preserving marking homeomorphisms
$h_{\rm in},h_{\rm out}$ carrying $P$ to the source and target
configurations in (A5), respectively, with
$$
h_{\rm in}(\Gamma)=\alpha_*,\qquad h_{\rm out}(\Gamma)=\gamma_*.
$$
Use change of coordinates: cut both spheres along the curves, match
the marked disks, and glue the boundary homeomorphisms.
Curves with the same label partition are not assumed isotopic.

The topological self-map
$$
G=h_{\rm out}^{-1}\circ R_{x_*}\circ h_{\rm in}
\tag{A7}
$$
has the same critical scheme (C3) as $F$.
Moreover, $G(\Gamma)=\Gamma$ with absolute degree $1$, and the other
pullback component is peripheral. Thus $\{\Gamma\}$ is a stable multicurve
with matrix $[1]$, a Levy obstruction.
All five marks lie in critical cycles and have orbifold weight $\infty$;
the orbifold Euler characteristic is $2-5=-3$.
Consequently, $G$ is not equivalent to a rational map.

It remains to verify that $G$ lies in the same pure Hurwitz class.
Join $p$ to $(s_*,t_*)$ by a path in connected $\mathcal U$.
The family $R_{t^2}$ along this path, with continuous source and target
markings, preserves all five label transitions. Transporting the markings
gives a covering equivalence. Any other final markings differ from the
transported ones by homeomorphisms fixing $P$ pointwise.
Hence, up to isotopy relative to $P$,
$$
G=u\circ F\circ v\qquad(u,v\in\mathcal G).
\tag{A8}
$$

Thus the Hurwitz biset $B(F)$ contains an obstructed element.
By Parry–Pilgrim, Theorem 1.2, $B(F)$ is not contracting.
This agrees with the direct check of $\varphi_F$ below.

# 6. Direct check of Pilgrim's criterion

Let $X\subset\mathcal C$ be the classes with two-point side $\{a_1,b_1\}$.
This is one $\mathcal G$-orbit: the same cutting-and-gluing argument
gives a pure homeomorphism between any two such curves.

**Lemma.** Every $\delta\in X$ has some $\gamma\in X$ whose essential
pullback is $\delta$ with degree $1$.

**Proof.** From (A8) and the fixed curve $\Gamma$ of $G$, obtain curves
for $F$ itself:
$$
\alpha=u^{-1}(\Gamma),\qquad\beta=v(\Gamma),\qquad
\beta\subset F^{-1}(\alpha),\quad \deg(F:\beta\to\alpha)=1.
$$
Both belong to $X$, since $u,v$ are pure.
Choose $a\in\mathcal G$ with $a(\beta)=\delta$.
Surjectivity in (A4) gives $h\in H$ with $\varphi_F(h)=a$.
Lifting gives equivariance
$$
\mathcal P_F(h(\alpha))=\varphi_F(h)(\mathcal P_F(\alpha)).
$$
By §3's lemma the essential component is unique, so $\gamma=h(\alpha)$ works. $\square$

Inductively, for every $n\ge1$ and fixed $\delta_0\in X$, choose
$$
\delta_n\longmapsto\delta_{n-1}\longmapsto\cdots
\longmapsto\delta_0,\qquad \delta_j\in X,
\tag{A9}
$$
where arrows denote pullback and every degree is $1$.
These are arbitrarily long finite chains; no single infinite forward
degree-one orbit is asserted.

Let $T_\delta$ be the positive Dehn twist.
Every curve in $X$ encloses both critical values, so its entire preimage
has two degree-one components. The twist lifts without taking an extra
power. One lifted twist is about the essential component; the other
is peripheral and trivial in $\mathcal G$. For (A9),
$$
T_{\delta_n}\in\operatorname{dom}(\varphi_F^n),\qquad
\varphi_F^n(T_{\delta_n}^{\,k})=T_{\delta_0}^{\,k}
\quad(k\in\mathbb Z).
\tag{A10}
$$

Fix a finite generating set of $\mathcal G$ with word norm $\|\cdot\|$.
Since $\delta_n,\delta_0$ belong to the same pure orbit, some $q_n\in\mathcal G$ gives
$$
T_{\delta_n}=q_nT_{\delta_0}q_n^{-1},\qquad
\left|\|T_{\delta_n}^{\,k}\|-\|T_{\delta_0}^{\,k}\|\right|
\le2\|q_n\|.
\tag{A11}
$$
An essential Dehn twist has infinite order.
Hence $\|T_{\delta_0}^{\,k}\|\to\infty$ as $|k|\to\infty$:
word-metric balls are finite and the powers are distinct.
For each fixed $n$, (A10)–(A11) imply
$$
\lim_{k\to\infty}
\frac{\|\varphi_F^n(T_{\delta_n}^{\,k})\|}
     {\|T_{\delta_n}^{\,k}\|}=1.
$$

Pilgrim's coefficient is defined by
$$
\rho(\varphi_F)=\limsup_{n\to\infty}
\left(
\limsup_{\substack{g\in\operatorname{dom}(\varphi_F^n)\\
                   \|g\|\to\infty}}
\frac{\|\varphi_F^n(g)\|}{\|g\|}
\right)^{1/n}.
$$
The inner limsup is at least $1$ for every $n$. Therefore,
$$
\boxed{\rho(\varphi_F)\ge1.}
\tag{A12}
$$

**Thus the hypothesis $\rho(\varphi_F)<1$ in Pilgrim's Theorem 1.4
is false for $F$.** It is no longer an unchecked programme item.

# 7. Simple proof strategies ruled out

The set $X$ is infinite. For example, twists about an intersecting curve
give infinitely many distinct classes with the same label partition;
intersection numbers distinguish them.

Suppose finite $\mathcal A$ is pullback-invariant and a proposed height
$h$ depends only on puncture partitions. Choose $\delta_0\in X-\mathcal A$.
For any fixed $q$, construct (A9) of length $q$.
None of its curves belongs to $\mathcal A$, since invariance would then
force $\delta_0\in\mathcal A$.
All have the same label partition and height, so
$$
h(\delta_0)=h(\delta_q),
$$
ruling out strict decrease after $q$ steps.

This excludes:

- A proof through ordinary contraction of $\varphi_F$.
- Strong contraction of all of $B(F)$.
- A strict height on just the ten two-point puncture partitions,
  even with any fixed pullback block length.
- A common upper bound on the length of consecutive degree-one pullbacks
  over all initial curves.

The last point does not contradict (A1), whose entry time may depend
on the initial curve.

# 8. The remaining new research step

Not yet constructed:

1. A finite explicit list $\mathcal A$.
2. Its complete transition graph for the fixed marking of $F$.
3. Control of unbounded twist parameters proving entry of every curve.

The audit's lemmas replace none of these tasks.
Failure of strong contraction does not disprove a weaker attractor.
In particular, the obstruction of $G$ in (A7) cannot be transferred to $F$.

The Pilgrim-criterion question is now settled negatively.
The next substantive experiment is geometric pullback of unbounded-twist
families for $F$ itself, retaining isotopy classes.
A bound or induction incorporating that parameter is then required.

No reduction of B3 was found within the audited theorems.
The later [literature screening](B3_publication_screening.md) supports
novelty of the full proposed theorem. The attractor and general proof
are still absent. No new general theorem about all Hurwitz bisets is claimed.

# 9. Reproducibility and audit scope

[b3_audit_compute.py](b3_audit_compute.py) checks exact identities for (A3),
the fixed point, rational parameters (A5)–(A6), and every marked-point
distribution in §3. The [reference data](B3_audit_data.json) contain only
these calculations. The topological steps and general conclusion (A12)
are proved in the text, not replaced by finite computation.
No Lean verification was performed.

~~~bash
python3 packages/pilgrim-bisets/research/b3_audit_compute.py --check
~~~

In addition to the primary sources above, the description of
[Pf4](https://sourceforge.net/projects/pf4/), cited by Parry–Pilgrim, was inspected.
Their computed strata scrambler concerns pure mapping-class multicurve
orbits and the entire Hurwitz biset. It is not the graph of all isotopy
classes under fixed $F$.
Pf4 source code was neither inspected nor run in this first audit.
The later [screening](B3_publication_screening.md), §5, includes static
inspection of the public 2.0 release.

Searches included "basilica rabbit curve attractor", "mating global curve
attractor", "basilica rabbit Hurwitz contracting", and references and
later work on Pilgrim's criterion. A missing search hit is not used as
proof of novelty. Established audit results are (A3), the lemmas in
§§3–6, and the exclusions in §7.