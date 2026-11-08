# Decision on B2-N

7 November 2026. Object: $H_m/D_{3,m}$ for the recursion
$a=(1,b)(01)$, $b=(1,a)$ over the free group $F=F(a,b)$.

**All proposed data can be computed for every $m$:** the full integral
image, derived subgroup, center, and abelian quotient. A proof and exact
reduction to known Basilica-group results follow.
**B2-N is closed as the primary paper candidate: the stated problem is
a consequence of a known mechanism.**

The previous comparison was incomplete: it cited Theorem 4.1 without
accounting for Theorem 4.7(i) and Corollary 4.11, or checking the passage
from the free group to the faithful action group. These steps are now
written out. The established reduction does not require the published
paper to state our final formula in exactly this form; no such attribution
is made here.

# Source and scope of the comparison

Di Domenico, Fernández-Alcober, Noce, Thillaisundaram,
[*p-Basilica Groups*](https://link.springer.com/article/10.1007/s00009-022-02187-z),
Mediterranean Journal of Mathematics 19, 275 (2022).
Page numbers below refer to the paper's 28-page PDF.
The required statements apply at $p=2$.

- **Theorem 4.7(i), p. 15**, and formula (4.7) in its proof:
  the image of the derived subgroup of the full level stabilizer is the
  product of derived subgroups at all vertices of that level.
- **Theorems 3.3 and 4.10(i), the latter on p. 17:**
  abelianization has two free generators; the commutator generates an
  infinite cyclic quotient modulo $\gamma_3$.
  **Corollary 4.11, p. 17**, identifies the quotient modulo $\gamma_3$
  with the integral Heisenberg group.
- **Theorem 4.5, p. 14:** every section of a full level stabilizer maps
  onto the whole group.

The authors use $a_{\rm old}=(1,b_{\rm old})$ and
$b_{\rm old}=(1,a_{\rm old})(01)$. Our generators satisfy
$a_{\rm old}=b$, $b_{\rm old}=a$. The right action and section rule
agree with (2.1) of the paper. Our $0,1$ are its first two alphabet letters.
Below, $\Gamma$ denotes the faithful action group; $F$ remains free.

# Exact statement

Put $X=\{0,1\}$ and $H_m=\ker(F\to\operatorname{Sym}(X^m))$;
$H_0=F$. This is the pointwise stabilizer of the **whole** level.
Sections satisfy

$$
(gh)|_s=(g|_s)(h|_{s^g}),\qquad [g,h]=g^{-1}h^{-1}gh.
$$

Let $\gamma_1(F)=F$, $\gamma_{n+1}(F)=[\gamma_n(F),F]$, and

$$
D_{3,m}=\{g\in H_m:g|_v\in\gamma_3(F)\text{ for every }|v|\le m\}.
$$

The section at the empty word is the element itself.
All sections of depth at most $m$ are homomorphisms on $H_m$, so
$D_{3,m}$ is a normal subgroup of $H_m$.
For comparison, write
$C_{n,m}=\{g\in H_m:g|_w\in\gamma_n(F)\text{ for every }w\in X^m\}$
for the kernel of the last-level conditions alone.

Use the model $Q=F/\gamma_3(F)=\mathbb Z^3$ with multiplication

$$
(x,y,z)(u,v,w)=(x+u,y+v,z+w+xv).
\tag{B1}
$$

Here $a=(1,0,0)$, $b=(0,1,0)$, $c=[a,b]=(0,0,1)$.
Put $k=2^m$ and let
$\pi:Q^{X^m}\to(\mathbb Z^2)^{X^m}$ be the coordinatewise projection
$(x,y,z)\mapsto(x,y)$.

Define the integral lattice $V_m\le(\mathbb Z^2)^{X^m}$.
For $\mathbf z=(z_w)_{w\in X^m}$ with $z_w=(x_w,y_w)$, write

$$
\Sigma_u(\mathbf z)=\sum_{\substack{w\in X^m\\u\text{ is a prefix of }w}}z_w,
\qquad T(x,y)=(y,x),\qquad \pi_b(x,y)=y.
$$

Then $V_m$ is defined by the following equalities over $\mathbb Z$:

$$
\pi_b T^{m-|u|-1}
\bigl(\Sigma_{u0}(\mathbf z)-\Sigma_{u1}(\mathbf z)\bigr)=0
\quad (|u|<m).
\tag{B2}
$$

At $m=0$ there are no conditions and $V_0=\mathbb Z^2$.

**Theorem.** For every $m\ge0$, the last-level section map induces an isomorphism

$$
J_m:=H_m/D_{3,m}\ \simeq\ \pi^{-1}(V_m)\le Q^{X^m}.
\tag{B3}
$$

This describes the entire group: multiplication is (B1) in each coordinate,
the conditions on $x_w,y_w$ are exactly (B2), and the $z$-coordinates
are arbitrary. In particular,

$$
J_m'=Z(J_m)\simeq\mathbb Z^{2^m},\qquad
J_m/J_m'\simeq\mathbb Z^{2^m+1},\qquad
h(J_m)=2^{m+1}+1.
\tag{B4}
$$

Here $h$ denotes Hirsch length. The group $J_m$ is finitely generated,
torsion-free, and nilpotent of class exactly $2$.

# Proof

## 1. The free class-2 quotient

In (B1), inversion is $(-x,-y,-z+xy)$ and the commutator of two elements
is $(0,0,xv-uy)$. Thus both the derived subgroup and the center are
$\{(0,0,z):z\in\mathbb Z\}$.

The map $q:F\to Q$ given by the stated images of $a,b$ kills $\gamma_3(F)$.
In $F/\gamma_3(F)$, $c$ is central and $ab=bac$, so collecting letters
puts every word in the form $a^x b^y c^t$. Its image in (B1) is
$(x,y,xy+t)$. Distinct triples $(x,y,t)$ have distinct images, and every
$(x,y,z)$ occurs with $t=z-xy$. Hence $\ker q=\gamma_3(F)$ and the model is exact.

## 2. Stabilizer image and abelian data

Let $\alpha:F\to\mathbb Z^2$ record exponent sums of $a,b$,
and $\beta=\pi_b\alpha$. We need three equalities:

$$
H_1=\langle b,a^2,aba^{-1}\rangle,
\qquad
\psi(b)=(1,a),\quad\psi(a^2)=(b,b),\quad
\psi(aba^{-1})=(a,1),
\tag{B5}
$$

$$
\psi(H_m)=\{(u,v)\in H_{m-1}^2:\beta(u)=\beta(v)\}\quad(m\ge1),
\tag{B6}
$$

$$
\alpha(g|_0)+\alpha(g|_1)=T\alpha(g)\quad(g\in F).
\tag{B7}
$$

For completeness, check them directly. The index of $H_1$ is two;
representatives $1,a$ give the generators in (B5) by Schreier rewriting.
The product rule gives their sections. The subgroup generated by the
three pairs in (B5) contains $\ker\beta\times\ker\beta$:
$\ker\beta$ is generated by $b^j a b^{-j}$. Indeed, reading a word
and moving accumulated powers of $b$ to the right replaces every
$a^{\pm1}$ by the appropriate conjugate, with residual exponent zero.
Conjugating $(a,1)$ and $(1,a)$ by powers of $(b,b)$ supplies these
generators independently in both coordinates. If $\beta(u)=\beta(v)=t$,
then $(u,v)=(ub^{-t},vb^{-t})(b,b)^t$ lies in that subgroup.
This proves (B6) at $m=1$. The general case follows because $g\in H_m$
means $g\in H_1$ and $g|_0,g|_1\in H_{m-1}$.
Finally, the sum on the left of (B7) is a homomorphism, since permuting
indices preserves the sum. Checking $a,b$ proves (B7).

Iterating (B7), using $T^2=1$, gives

$$
\alpha(g|_u)=T^{m-|u|}\Sigma_u
\bigl((\alpha(g|_w))_{w\in X^m}\bigr)\quad(|u|\le m).
\tag{B8}
$$

We show that $V_m$ is the **exact** image of abelian sections of $H_m$
at level $m$. This holds at $m=0$. Inductively, the two collections in
subtrees $0,1$ lift to $u,v\in H_{m-1}$. All conditions (B2) except
the root condition say precisely that they belong to $V_{m-1}$.
By (B8), the root condition is $\beta(u)=\beta(v)$.
By (B6), this pair lifts to $H_m$. The same equalities give the reverse
inclusion. No division or finite-index argument is involved.

Let $r_m=\operatorname{rank}V_m$ and
$f_m(\mathbf z)=\pi_b T^m\Sigma_{\varnothing}(\mathbf z)$ on $V_m$.
By (B8), this is the root exponent of $b$. It is nonzero: if $e>0$ is
the order of the action of $b$ on level $m$, then $b^e\in H_m$ and
$f_m$ takes the value $e$. By (B6),

$$
V_m\simeq\ker\bigl(V_{m-1}^2\to f_{m-1}(V_{m-1}),\
(p,q)\mapsto f_{m-1}(p)-f_{m-1}(q)\bigr).
$$

The arrow is surjective with infinite cyclic image.
Thus $r_m=2r_{m-1}-1$, $r_0=2$, giving $r_m=2^m+1$.
The lattice $V_m$ is saturated: it is the kernel of the integral
linear map (B2), so $n\mathbf z\in V_m$, $n\ne0$, implies $\mathbf z\in V_m$.

## 3. Recovering the root in the Heisenberg group

On the fiber product
$P=\{(u,v)\in Q^2:\pi_b\pi(u)=\pi_b\pi(v)\}$, define

$$
R\bigl((x,t,z),(y,t,w)\bigr)
=\bigl(2t,\ x+y,\ x+2t(x+y)-2(z+w)\bigr).
\tag{B9}
$$

Here $\pi$ on one coordinate means $(x,y,z)\mapsto(x,y)$.
This is a homomorphism: multiplying two pairs with parameters
$x,y,t,z,w$ and $x',y',t',z',w'$ gives the parameters

$$
x+x',\quad y+y',\quad t+t',\quad
z+z'+xt',\quad w+w'+yt'.
$$

Substituting into the third coordinate of (B9) gives the sum of the old
third coordinates plus $2t(x'+y')$, as required by (B1).
The first two coordinates add. On $(1,a),(b,b),(a,1)$, the values of
$R$ are respectively $b,a^2,aba^{-1}$ in $Q$; the last triple is $(0,1,1)$.
By (B5), as an equality of homomorphisms on $H_1$,

$$
q(g)=R\bigl(q(g|_0),q(g|_1)\bigr)\quad(g\in H_1).
\tag{B10}
$$

Put

$$
\tau_m:H_m\to Q^{X^m},\qquad
\tau_m(g)=\bigl(q(g|_w)\bigr)_{w\in X^m}.
$$

This is a homomorphism. If every coordinate is the identity, (B10)
successively recovers the identity at all preceding vertices.
It applies because, for $|u|<m$, the section $g|_u$ belongs to
$H_{m-|u|}\subseteq H_1$. Therefore

$$
\ker\tau_m=D_{3,m}.
\tag{B11}
$$

This also proves $D_{3,m}=C_{3,m}$: last-level conditions suffice.
At $m=0$, the assertion is $\ker q=\gamma_3(F)$.

## 4. Integral generators of the derived subgroup

The next construction is formula (4.7) in the proof of Theorem 4.7(i)
of the cited paper, after renaming generators. We check it directly
in the free group to exclude any issue in passing to the faithful action.

Put $w_0=[a,b]$ and

$$
w_{2r}=[a^{2^r},b^{2^r}]\quad(r\ge1),\qquad
w_{2r+1}=[b^{2^r},a^{2^{r+1}}]\quad(r\ge0).
\tag{B12}
$$

The recursions $a^{2t}=(b^t,b^t)$, $b^t=(1,a^t)$ give

$$
\operatorname{ord}\rho_m(a)=2^{\lceil m/2\rceil},\qquad
\operatorname{ord}\rho_m(b)=2^{\lfloor m/2\rfloor}.
\tag{B13}
$$

At $m=0$, both orders are $1$. For $m\ge1$, the order of $b$ equals
the previous-level order of $a$, while the order of $a$ is twice the
previous-level order of $b$. Odd powers of $a$ have nontrivial root
permutation; for even powers, use the displayed recursion.
This proves (B13) inductively. Both arguments of each commutator in
(B12) therefore lie in $H_m$, so $w_m\in H_m'$.

Both arguments fix the first level, so their commutator is computed
coordinatewise. The same recursions give $\psi(w_m)=(1,w_{m-1})$
for $m\ge1$. Thus the level-$m$ sections of $w_m$ are trivial except
at $1^m$, where the section is $c=[a,b]$.

The action of $F$ is transitive on each level. At the first level use $a$;
both projections $\psi(H_1)\to F$ are surjective by (B6).
For induction, first move the first letter, then move the suffix using
an element of $H_1$ with the required section.
Conjugating $w_m$ by an element moving $1^m$ to a chosen leaf makes
the unique nontrivial section a conjugate of $c$. In $Q$, it remains $c$
because $c$ is central. Since $H_m'$ is normal in $F$, every leaf has
an element of $H_m'$ with unit central vector at that leaf.

Every commutator in $Q^{X^m}$ is central. Consequently,

$$
\tau_m(H_m')=Z(Q)^{X^m}\simeq\mathbb Z^k.
\tag{B14}
$$

This equality is integral: each leaf receives $c$ itself, without
multiplication by a nonzero coefficient.

## 5. Full image, center, and abelian quotient

Part 2 gives $\pi\tau_m(H_m)=V_m$. By (B14), the image of $\tau_m$
contains all of $\ker\pi$. Given $h\in\pi^{-1}(V_m)$, choose
$g\in H_m$ with $\pi\tau_m(g)=\pi(h)$.
Then $h\tau_m(g)^{-1}\in\ker\pi\subseteq\tau_m(H_m)$,
so $h\in\tau_m(H_m)$. Together with (B11), this proves (B3).

A surjective homomorphism maps the derived subgroup onto the derived
subgroup. Thus (B14) gives $J_m'=\ker\pi\simeq\mathbb Z^k$,
with quotient $V_m$.
Every section projection $H_m\to F$, $g\mapsto g|_w$, is surjective:
by (B6), any $u\in H_{m-1}$ lifts as the pair $(u,u)$; repeat along
the chosen leaf. Hence every projection $J_m\to Q$ is surjective.
A central element of $J_m$ therefore has each coordinate commuting
with all of $Q$, hence lying in $Z(Q)$. The reverse inclusion follows
from (B14), giving $Z(J_m)=J_m'$.

The group $V_m$ is free of rank $k+1$. Lift a basis and add the $k$
central generators to obtain a finite generating set of $J_m$.
The group $Q$ is torsion-free: the formula for powers first forces
$x=y=0$, then $z=0$. Its subgroup $J_m\le Q^k$ is therefore torsion-free.
The derived subgroup is nonzero and central, so the class is exactly $2$.
The Hirsch length of the central extension is $k+(k+1)=2k+1$.
This completes (B4).

# Why the free group creates no new case here

Let $p:F\twoheadrightarrow\Gamma$ map onto the faithful action group,
and let $K=\ker p$. By Theorems 3.3 and 4.10(i) of the source, the natural map

$$
F/\gamma_3(F)\longrightarrow\Gamma/\gamma_3(\Gamma)
\tag{B15}
$$

is an isomorphism **with the specified generator images**.
Indeed, if the normal form $a^x b^y c^t$ maps to the identity,
abelianization of $\Gamma$ gives $x=y=0$, and the infinite order of
the image of $c$ gives $t=0$. Surjectivity is immediate.
Thus $K\subseteq\gamma_3(F)$, refining the identification in Corollary 4.11.

The action kernel is closed under sections: every section of an
automorphism trivial on the whole tree is trivial too.
Hence $K\subseteq D_{3,m}$ for every $m$.
Also $H_m=p^{-1}(\operatorname{St}_\Gamma(m))$, sections commute with $p$,
and (B15) gives $p^{-1}(\gamma_3(\Gamma))=\gamma_3(F)$.
Therefore

$$
H_m/D_{3,m}\simeq
\operatorname{St}_\Gamma(m)/\overline D_{3,m},
$$

where $\overline D_{3,m}$ is defined by the same section conditions in
$\Gamma$. Finally, $p(H_m')=\operatorname{St}_\Gamma(m)'$.
Theorem 4.7(i) and (B15) immediately imply (B14); Theorem 4.5 supplies
the section surjectivity used above. Conditions (B2) follow from the
first stabilizer description and (B7); reconstruction (B9) is a check
on the three generators (B5).

Every computational step now has a complete argument and a close known
mechanism. Passing between $F$ and $\Gamma$ in class $2$ leaves no
additional research claim.

# Boundary of the passage to the next class

This calculation does not automatically extend to $\gamma_4$. For example,

$$
r=[b,aba^{-1}]
$$

belongs to $K$: it fixes the first level and has sections $1,1$ by (B5).
However, $r\notin\gamma_4(F)$.
Verify this using the Magnus substitution $a\mapsto1+A$, $b\mapsto1+B$
in noncommutative power series:

$$
\mu(r)=1+2BAB-BBA-ABB+\text{terms of degree at least }4.
$$

Let $I$ be the ideal of series with zero constant term.
The image of $\gamma_4(F)$ has no degree-$1$, $2$, or $3$ terms:
a commutator of series in $1+I^i$ and $1+I^j$ lies in $1+I^{i+j}$.
The nonzero cubic term excludes $r\in\gamma_4(F)$.
Meanwhile $r\in\gamma_3(F)$, since $b$ and $aba^{-1}=bc$ commute in
the class-$2$ quotient. Thus $K\nsubseteq\gamma_4(F)$; for $m\ge1$,
$r$ satisfies every last-section condition but not the root condition
modulo $\gamma_4$. Neither (B15) nor $C_{4,m}=D_{4,m}$ extends by this method.
This identifies the proof's boundary; no independent new result for
the next class is claimed here.

# Reproducible checks

The script **b2_compute.py** uses free words from **b1_compute.py** and
integer triples (B1). It checks:

- The homomorphism identity (B9) on every pair from the $3^5$ parameter
  choices $-1,0,1$, and compatibility with lifts of short words.
- Abelian section ranks at depths $0,1,2,3$.
- An explicit conjugate commutator for every leaf at those depths,
  giving central coefficient exactly $1$.
- Root-coordinate reconstruction for these witnesses and the cubic term
  of $\mu(r)$, using independent multiplication of truncated series.

| $m$ | $\operatorname{rank}J_m^{\rm ab}$ | $\operatorname{rank}J_m'$ | $h(J_m)$ |
| --- | --- | --- | --- |
| 0 | 2 | 1 | 3 |
| 1 | 3 | 2 | 5 |
| 2 | 5 | 4 | 9 |
| 3 | 9 | 8 | 17 |

Run from the project root:

~~~bash
python3 study/research/b2_compute.py --check
~~~

The exact reference data are **B2_calculations.json**.
These finite checks verify conventions and computations; the all-$m$
statement is proved above. Lean verification has not been performed.

# Additional comparisons and the decision

The following primary sources were also checked by 7 November 2026:

- Eick–Hartung, with an appendix by Bartholdi,
  [*A nilpotent quotient algorithm for L-presented groups*, version 2](https://arxiv.org/abs/0706.3131v2),
  §7.1, pp. 8–10, Table 1, and Conjecture 11.
  This concerns ordinary nilpotent quotients of the Basilica group,
  whose definitions differ from the all-sections kernel $D_{3,m}$.
  Algorithmic computability alone did not reduce our candidate.
- Hartung,
  [*Approximating the Schur multiplier of certain infinitely presented groups via nilpotent quotients*](https://arxiv.org/abs/1106.1098),
  §6, p. 11, Conjecture D. Its Dwyer quotients of the Schur multiplier
  are a different object.

Searches combined Basilica with "nilpotent portraits", "Heisenberg stabilizer",
and "nilpotent quotients lower central".
The decision rests on the proved reduction to Theorem 4.7(i) and the
Heisenberg quotient. Search results are not used to establish the absence
of predecessors. The 2026 status of the papers' older conjectures was not audited.

**Programme decision.** B1-R and B2-N remain completed examples.
A new primary candidate first needs an exact statement, its closest theorem,
and a specific claim beyond that theorem's consequences.
Moving to the next lower-central-series term alone does not provide such
a statement. No external feedback on this audit has been received.