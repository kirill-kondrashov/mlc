# How to use this worked example

The main topic is now bisets and compatible group quotients.
The geometric candidate T1 is retained as a reserve.

**Update after preparing this example:** B1-R has been proved completely
and retired from the main research route.
See the [audit and proof](B1_novelty_audit.md), [PDF](../novelty_audit.pdf).
The initial sessions, conjecture, and intermediate statuses are preserved below.

This is a model of five working sessions, with planned durations totaling
13 hours. The proofs and finite computations were actually carried out
while preparing the document. Their allocation to days models the organization
of work. No actual user sessions have been entered in the log.
Proceeding to the next session requires understanding the preceding one.

| Session | Time | Written output |
| --- | --- | --- |
| 1 | 2 h | Conventions, exact object, initial conjecture |
| 2 | 2 h | Explicit counterexample to descent to abelianization |
| 3 | 3 h | Admissible quotient criterion and its source |
| 4 | 3 h | Corrected construction and verification of its properties |
| 5 | 3 h | Small computations, upper bound, next question |

The initial lemmas provide a checked foundation; no scientific novelty
is claimed for them. The rank formula is proposed as a conjecture at the
end of session five. Its later audit and complete proof appear separately.

# Session 1. Specify the object and venture an exact conjecture

## Question before opening a book

"A group has a lower central series. Can we successively replace the group
by its nilpotent quotients while preserving the biset recursion?"

This asks about a specific operation on a biset.
A first check needs only a free group, a commutator, and two states.

## Conventions on the first page

Let $G$ be a group, $X=\{0,1\}$, and $B$ a left-free $G$–$G$-biset
with basis $\{b_0,b_1\}$. Every element of $B$ has a unique expression
$h b_s$, where $h\in G$, $s\in X$.
The left and right actions commute.

For $g\in G$, define a permutation $\rho(g)$ of $X$ and sections $g|_s\in G$ by

$$
b_s g=(g|_s)b_{s^g}.
$$

We write the action on the right. Associativity therefore gives

$$
s^{gh}=(s^g)^h,\qquad
(gh)|_s=(g|_s)(h|_{s^g}).
\tag{1}
$$

Indeed,

$$
b_s(gh)=(b_sg)h
=(g|_s)(b_{s^g}h)
=(g|_s)(h|_{s^g})b_{(s^g)^h}.
$$

Uniqueness of the basis expression gives both formulas.
Substituting $h=g^{-1}$ yields

$$
(g^{-1})|_s=\bigl(g|_{s^{g^{-1}}}\bigr)^{-1}.
\tag{2}
$$

This is the first useful result: the multiplication order for every
subsequent computation has been fixed.

## A concrete biset

Take the **free** group $G=F(a,b)$ and define

$$
\psi(a)=(1,b)(01),\qquad \psi(b)=(1,a).
\tag{3}
$$

Transition table:

| Element | $0^g$ | $g|_0$ | $1^g$ | $g|_1$ |
| --- | --- | --- | --- | --- |
| $a$ | $1$ | $1$ | $0$ | $b$ |
| $b$ | $0$ | $1$ | $1$ | $a$ |
| $a^{-1}$ | $1$ | $b^{-1}$ | $0$ | $1$ |
| $b^{-1}$ | $0$ | $1$ | $1$ | $a^{-1}$ |

Freeness of $F(a,b)$ extends the generator data to a homomorphism into
the wreath product. Equivalently, set $B=G\times X$, let the left action
multiply the first coordinate, and define the generators' right actions
by the table. These actions are invertible and commute with the left action;
the universal property of the free group supplies the right action of $G$.

This is a Basilica-type recursion. No additional relations from its faithful
tree action are imposed yet. All computations remain in the free group.
Related recursions in the literature often use different generator orders,
letters, or action conventions.

For comparison, Benli–Grigorchuk–de la Harpe, Example 2.17, use
$(b,1)(01)$ and $(a,1)$. Exchanging the two letters gives the form (3),
after matching the action convention.
See the [primary source](https://link.springer.com/article/10.1007/s13373-013-0031-5).
The algebraic results below need no geometric identification.

## First attempt

Let $\gamma_1(G)=G$, $\gamma_{n+1}(G)=[\gamma_n(G),G]$.
Try the following claim:

> Recursion (3) descends to every $G/\gamma_n(G)$ with the same two basis elements.

A possible first argument is: "$\gamma_n(G)$ is characteristic, so the
construction is well-defined." Stop here. A section map $g\mapsto g|_s$
is generally not a homomorphism on the whole group: the second index in (1)
depends on $g$. Being characteristic does not establish the required claim
about sections.

**End-of-session note:** test $\gamma_2(G)=[G,G]$ on one commutator.
Read the definitions of wreath products and sections;
general renormalization theory is not used at this stage.

# Session 2. A computation disproving the conjecture

## Read the word letter by letter

Choose the convention

$$
c=[a,b]=a^{-1}b^{-1}ab.
$$

Use the session-one table and rule (1).

| Before | Letter | After | Accumulated section |
| --- | --- | --- | --- |
| $0$ | $a^{-1}$ | $1$ | $b^{-1}$ |
| $1$ | $b^{-1}$ | $1$ | $b^{-1}a^{-1}$ |
| $1$ | $a$ | $0$ | $b^{-1}a^{-1}b$ |
| $0$ | $b$ | $0$ | $b^{-1}a^{-1}b$ |
| $1$ | $a^{-1}$ | $0$ | $1$ |
| $0$ | $b^{-1}$ | $0$ | $1$ |
| $0$ | $a$ | $1$ | $1$ |
| $1$ | $b$ | $1$ | $a$ |

The first four rows start at $0$; the last four start at $1$.
The exact equality is

$$
\psi(c)=(b^{-1}a^{-1}b,\ a)
\quad\text{with identity permutation}.
\tag{4}
$$

## Why this suffices

Write

$$
\alpha:G\longrightarrow G_{\rm ab}\simeq\mathbb Z^2
$$

for the homomorphism recording exponent sums of $a,b$.
Its kernel is $[G,G]$: the universal abelian quotient of the free group
has free basis $\bar a,\bar b$.

Although $c\in[G,G]$, equality (4) gives

$$
\alpha(c|_0)=(-1,0),\qquad \alpha(c|_1)=(1,0).
\tag{5}
$$

In $G/[G,G]$, the element $c$ must become the identity.
The identity recursion has trivial sections, whereas (5) gives nonzero ones.
Thus the proposed descent to abelianization is **impossible while retaining
this basis**.

The first conjecture is disproved for this concrete biset.

## Another attempt: the double quotient

The double orbit set $N\backslash B/N$, where $N=[G,G]$, exists because
the actions commute. Check whether left-freeness survives.

The equality $b_1c=a b_1$ gives $[b_1]=[a b_1]$ in the double quotient,
while $\bar a\ne1$ in $G/N$.
Thus the nonidentity element $\bar a$ stabilizes $[b_1]$.
The left $G/N$-action is no longer free.

**End-of-session note:** the orbit set exists, but the required class of
bisets is not preserved. The next task is to derive the exact quotient criterion.

# Session 3. The correct criterion and reading for a specific dependency

## Quotient lemma

**Lemma Q.** Let $B$ be a left-free $G$–$G$-biset with finite basis $X$,
and let $N\triangleleft G$. The right $G$-action on the left quotient
$N\backslash B$ descends to $G/N$ if and only if

$$
\forall n\in N,\ \forall s\in X:\qquad
s^n=s,\quad n|_s\in N.
\tag{6}
$$

When (6) holds, this is a left-free $(G/N)$–$(G/N)$-biset with the same
number of basis elements.

**Proof.** The right $G$-action on $N\backslash B$ is well-defined:
if $b'=nb$, then $b'g=n(bg)$.
Normality of $N$ makes the left $G/N$-action well-defined.
The expression $B=G\times X$ identifies the left quotient with
$(G/N)\times X$, whose left action is free.

The right action descends to $G/N$ exactly when every $n\in N$ fixes
every element of $N\backslash B$. For a basis element, this says

$$
N b_s n=N b_s.
$$

Since $b_sn=(n|_s)b_{s^n}$, uniqueness of the orbit expression gives
exactly (6). Checking the basis suffices: for $h\in G$,

$$
N(hb_s)n=N h(n|_s)b_s=N h b_s,
$$

because $h(n|_s)h^{-1}\in N$.
Thus every element of the left quotient is fixed, proving both directions. $\square$

This concerns the canonical left quotient retaining the orbit basis.
More general operations may change the number of orbits.

## Independence of the basis

Write a new basis as $b'_s=u_s b_{\pi(s)}$, where $\pi$ is a permutation.
If $\pi(t)=\pi(s)^g$, then

$$
b'_s g
=u_s(g|_{\pi(s)})u_t^{-1}b'_t.
\tag{7}
$$

For $n$ fixing the old basis index, $t=s$.
The new section is therefore $u_s(n|_{\pi(s)})u_s^{-1}$.
Normality of $N$ shows that membership of sections in $N$ is independent
of the basis. The identity permutation condition is preserved as well.

## What to read and record

The early author version of Nekrashevych's *Self-similar groups*,
§2.7.3, **Proposition 2.7.4, printed pp. 40–41**, gives the normal-subgroup
invariance condition and the consequence for the action kernel.
[Author PDF](https://www.math.stonybrook.edu/~mlyubich/Archive/Stock/Nekrash.pdf).
These are PDF pages 50–51, counted from one.

Nekrashevych uses a free right action and writes the tree action on the left.
Compare our lemma with the opposite biset.
Formulas (1) and (7) were derived afresh in our convention.
The numbering belongs to that early version and must be checked before
using it for another edition.

Record in the source card:

- Known result: normality together with invariance under sections.
- Lemma Q is its elementary form for the canonical quotient.
- No novelty is claimed for Q.
- The initial conjecture was disproved by computation (4).

## A stronger obstruction

If (6) holds, every $n\in N$ fixes every finite word.
Induct on its length. The first letter is fixed by (6);
the section $n|_s\in N$ acts on the remaining word. Therefore

$$
N\subseteq\ker\bigl(G\curvearrowright X^*\bigr).
\tag{8}
$$

If the tree action is faithful, only $N=1$ is admissible.
Consequently, no sequence of nontrivial canonical quotients of the faithful
group can retain this basis. Our original group is free; its action is not
assumed faithful. Replacing it by the faithful action group in (5) requires
a separate verification.

**End-of-session note:** the condition has been located in the literature.
For approximations, change the construction while retaining which side
of the biset is being quotiented.

# Session 4. Correct the construction and prove it is well-defined

## Replacing the group on one side

Let $n\ge1$, $Q_n=G/\gamma_n(G)$.
The left quotient $\gamma_n(G)\backslash B$ always has a free left
$Q_n$-action and a right action of the original $G$.

Project the recursion **in the output sections**:

$$
G\xrightarrow{\psi}G^X\rtimes\operatorname{Sym}(X)
\longrightarrow Q_n^X\rtimes\operatorname{Sym}(X).
$$

Let $C_{n,1}$ be the kernel of this homomorphism.
The right action factors through $G/C_{n,1}$, producing the biset

$$
{}_{Q_n}\bigl(\gamma_n(G)\backslash B\bigr)_{G/C_{n,1}}.
\tag{9}
$$

The groups on the two sides differ. This is what avoids the session-two
obstruction. Recursion (3) has not been declared a recursion over
$G/\gamma_n(G)$ on both sides.

The kernel $C_{n,1}$ is normal. After a basis change, (7) conjugates the
projected recursion, so the kernel is unchanged.
These are properties of the canonical quotient just constructed.

## Approximation through depth $m$

The recursion defines sections $g|_v$ for every $v\in X^*$ and actions
$\rho_m$ on $X^m$. Set $\psi_0=\operatorname{id}_G$.
For $m\ge0$, define

$$
C_{n,m}=
\ker\left(G\longrightarrow Q_n^{X^m}\rtimes\operatorname{Sym}(X^m)\right),
$$

$$
D_{n,m}=\bigcap_{j=0}^{m}C_{n,j},\qquad C_{n,0}=\gamma_n(G).
\tag{10}
$$

The intersection is deliberate: for a general recursion, the individual
$C_{n,m}$ need not decrease with $m$. For example, for
$G=\mathbb Z=\langle t\rangle$, $\psi(t)=(1,1)(01)$, and $n=2$,
we have $C_{2,0}=0$, $C_{2,1}=2\mathbb Z$.

The groups $D_{n,m}$ are normal and decrease with $m$.
To check basis independence, note that $B^{\otimes m}$ is left-free
with basis indexed by $X^m$. In $B\otimes_G B$, writing the second
factor as $h b_s$ moves $h$ into the first factor by the balancing
relation; then use its unique basis expression. This proves the claim
by induction on $m$.

Two tensor-power bases satisfy $b'_v=u_vb_{\pi(v)}$.
By (7), the permutations of $X^m$ are conjugate and have the same kernel.
For an element of that kernel, new sections are conjugates of the old
sections with permuted indices. Normality of $\gamma_n(G)$ preserves
section membership in that subgroup. Thus every $C_{n,m}$ and their
intersection $D_{n,m}$ are basis-independent.

Write $H_m=\ker\rho_m$ for the **pointwise stabilizer of the whole level**.
It has finite index. On $H_m$, all maps $g\mapsto g|_v$, $|v|\le m$,
are homomorphisms, because the index $v$ in (1) is fixed.

For $g\in H_m$, membership in $D_{n,m}$ means
$g|_v\in\gamma_n(G)$ for every $|v|\le m$. Consequently,

$$
\gamma_n(H_m)\subseteq D_{n,m}\subseteq H_m.
\tag{11}
$$

The first assertion follows from functoriality of the lower central
series under the section homomorphisms. More precisely,

$$
H_m/D_{n,m}\hookrightarrow
\prod_{|v|\le m}G/\gamma_n(G).
\tag{12}
$$

Thus $G/D_{n,m}$ is virtually nilpotent of class at most $n-1$:
it has the finite-index subgroup (12), which embeds in a product of
nilpotent groups of that class. This does not assert finiteness of $G/D_{n,m}$.

## A computable abelian case

For $G=F(a,b)$ and $n=2$, introduce

$$
\Lambda_m:H_m\longrightarrow
\bigoplus_{|v|\le m}\mathbb Z^2,\qquad
g\longmapsto\bigl(\alpha(g|_v)\bigr)_{|v|\le m}.
\tag{13}
$$

This is a homomorphism because every index is fixed. From (10),

$$
\ker\Lambda_m=D_{2,m},\qquad
H_m/D_{2,m}\simeq\operatorname{im}\Lambda_m.
\tag{14}
$$

The image is a finitely generated free abelian group, being a subgroup
of a finite-rank free abelian group. Denote its rank by $r_m$.

We have obtained an exact finite numerical invariant to test on examples.
It concerns this biset over the free group. Neither local connectivity
nor MLC follows from it without additional theorems.

**End-of-session note:** compute $r_1$ by hand; then obtain several exact
values of $r_m$ and seek a general bound.

# Session 5. Complete a proof in a small case

## First-level stabilizer generators

In (3), $\rho(a)=(01)$ and $\rho(b)=1$.
Thus $H_1$ is the kernel of the exponent sum of $a$ modulo $2$.
It is generated by

$$
h_1=b,\qquad h_2=a^2,\qquad h_3=aba^{-1}.
\tag{15}
$$

To check generation, take coset representatives $t_0=1$, $t_1=a$.
Track the parity of the number of $a^{\pm1}$ letters.
For positive letters, the corrections $t_\varepsilon g t_{\varepsilon'}^{-1}$ are

| Current state | Letter | Correction |
| --- | --- | --- |
| $0$ | $a$ | $1$ |
| $0$ | $b$ | $b$ |
| $1$ | $a$ | $a^2$ |
| $1$ | $b$ | $aba^{-1}$ |

For an inverse letter, use the inverse correction for the reversed transition.
Adjacent representatives cancel in the product of corrections.
For a word in $H_1$, initial and final states are $0$, expressing the
word through (15) and their inverses. This proves generation.

Using (1), we compute

$$
\psi(h_1)=(1,a),\quad
\psi(h_2)=(b,b),\quad
\psi(h_3)=(a,1),
\tag{16}
$$

with all permutations trivial. The values of $\Lambda_1$, in coordinate
order "root, $0$, $1$", are

$$
\begin{aligned}
\Lambda_1(h_1)&=(0,1;\ 0,0;\ 1,0),\\
\Lambda_1(h_2)&=(2,0;\ 0,1;\ 0,1),\\
\Lambda_1(h_3)&=(0,1;\ 1,0;\ 0,0).
\end{aligned}
\tag{17}
$$

Choose coordinates "root $a$", "$a$ in section $0$", and "$a$ in section $1$".
The corresponding rows are $(0,0,1)$, $(2,0,0)$, $(0,1,0)$, with determinant $2$.
Thus the three vectors are independent over $\mathbb Q$.
Generation by (15) gives $r_1\le3$; independence gives $r_1\ge3$.
Hence **$r_1=3$**.

We also obtain the sharper assertion

$$
D_{2,1}=[H_1,H_1].
\tag{18}
$$

Indeed, the homomorphism $\mathbb Z^3\to (H_1)_{\rm ab}$ defined by (15)
is surjective. Its composite with $\Lambda_1$ is injective by independence
in (17). The first homomorphism is therefore an isomorphism, and the
induced map $(H_1)_{\rm ab}\to\mathbb Z^6$ is injective.
The kernel of $\Lambda_1$ is exactly the derived subgroup of $H_1$;
apply (14).

## Summing sections gives another checkable lemma

For any finite-rank left-free $G$–$G$-biset, write
$\alpha:G\to G_{\rm ab}$ for the canonical projection and put

$$
S(g)=\sum_{s\in X}\alpha(g|_s)\in G_{\rm ab}.
$$

Rule (1) gives

$$
S(gh)=\sum_s\alpha(g|_s)+\sum_s\alpha(h|_{s^g})
=S(g)+S(h).
$$

Thus $S$ is a homomorphism to an abelian group and factors through abelianization:

$$
S=T_B\circ\alpha,\qquad T_B:G_{\rm ab}\to G_{\rm ab}.
\tag{19}
$$

Under a basis change, (7) adds
$\sum_s\alpha(u_s)-\sum_s\alpha(u_t)$, which cancels because
$s\mapsto t$ is a permutation. Hence $T_B$ is basis-independent.

For (3), the section sums of the generators are respectively $\bar b$ and $\bar a$:

$$
T_B(u,v)=(v,u),\qquad T_B^2=1.
\tag{20}
$$

Induction using (19) gives, for every $g\in G$ and $k\ge0$,

$$
\sum_{|w|=k}\alpha(g|_w)=T_B^k\alpha(g).
\tag{21}
$$

Consequently, abelian images of intermediate sections can be recovered
from the last-level sections. In this example, the rank in (13) can be
computed using the last level alone. In particular, $D_{2,m}=C_{2,m}$
for this recursion: identity permutation at level $m$ implies identity
at earlier levels, and (20)–(21) recover zero images for the intermediate
sections. At $m=0$, the equality follows from the definition.

Identifying (19) with a specific transfer-map convention in the literature
requires a comparison. A recent source is Miller–Steinberg,
[arXiv:2409.02359v3](https://arxiv.org/abs/2409.02359v3).

## Obtain a general upper bound

From (16), for every $h\in H_1$,

$$
\beta\alpha(h|_0)=\beta\alpha(h|_1),
\tag{22}
$$

where $\beta:\mathbb Z^2\to\mathbb Z$ is the second coordinate.
It suffices to check this on the generators (15), since both sides
are homomorphisms on $H_1$.

**Lemma U.** For recursion (3) and every $m\ge0$,

$$
r_m\le2^m+1.
\tag{23}
$$

**Proof.** At $m=0$, the abelianization of $F(a,b)$ has rank $2$.
Let $m\ge1$, $g\in H_m$, and put $z_w=\alpha(g|_w)\in\mathbb Q^2$
for $|w|=m$. By (21) and $T_B^{-1}=T_B$, for each prefix $u$,

$$
\alpha(g|_u)
=T_B^{\,m-|u|}
\sum_{|w|=m-|u|}z_{uw}.
\tag{24}
$$

If $|v|<m$, the section $g|_v$ fixes the first level.
Apply (22) to this section and (24) to its children to obtain

$$
\beta T_B^{\,m-|v|-1}
\left(
\sum_{|w|=m-|v|-1}z_{v0w}
-
\sum_{|w|=m-|v|-1}z_{v1w}
\right)=0.
\tag{25}
$$

The functional $\beta T_B^k$ selects the $b$-coordinate for even $k$
and the $a$-coordinate for odd $k$. Each internal vertex $v$ defines
a coefficient row: $+1$ on leaves of its left subtree, $-1$ on leaves
of its right subtree, and $0$ elsewhere, in the selected coordinate.

These rows are linearly independent. Rows using different coordinates
have zero scalar product. For one coordinate, the subtrees are either
disjoint or nested. A nested row has zero sum on its support, whereas
the outer row is constant there; the scalar product again vanishes.
Each row has positive squared norm. Hence the rows are nonzero and
pairwise orthogonal over $\mathbb Q$.

There are $2^m-1$ internal vertices and $2^{m+1}$ coordinates in
$(z_w)_{|w|=m}$. The admissible-vector space therefore has dimension at most

$$
2^{m+1}-(2^m-1)=2^m+1.
$$

The last-level image lies in this space. By (24), it injectively determines
the full image of $\Lambda_m$, so their ranks agree. This proves (23). $\square$

At this stage, a lower bound for all $m$ is still needed; finite examples
do not provide it. The subsequent proof appears in the audit.
It has not yet been determined whether Lemma U is explicitly or implicitly
contained in existing results on the Basilica recursion.

## Computations to check the argument and formulate the next conjecture

The script **b1_compute.py** uses only the Python standard library
and exact rational arithmetic. It:

1. Constructs the finite image $\rho_m(G)$.
2. Chooses representatives by traversing its Cayley graph.
3. Computes Schreier generators of $H_m$.
4. Computes the vectors (13) on those generators.
5. Finds the matrix rank over $\mathbb Q$.

Stabilizer generation follows from the same telescoping rewriting used
for (15), now with representatives for the whole finite image.
A generating set suffices because its images generate $\Lambda_m(H_m)$.
The number of nontrivial Schreier generators is $[G:H_m]+1$, as follows
from a spanning tree in the Cayley graph of a rank-$2$ free group.

Results:

| $m$ | $[G:H_m]$ | Schreier generators | Coordinates in (13) | $r_m$ |
| --- | --- | --- | --- | --- |
| 0 | 1 | 2 | 2 | 2 |
| 1 | 2 | 3 | 6 | 3 |
| 2 | 8 | 9 | 14 | 5 |
| 3 | 64 | 65 | 30 | 9 |

Distinguish the stabilizer index of the **whole level** from that of
**one vertex**. The table contains $1,2,8,64$; these cannot be replaced by $2^m$.

Check the saved results from the repository root:

~~~bash
python3 study/research/b1_compute.py --check
~~~

The script also compares the composed recursion with letter-by-letter
action on finite words, checks the hand computation (4), and repeats
rank calculations modulo $101$ and $103$. The two action methods are
compared on all generator words of length at most $3$ and vertices
of depth at most $4$.
These checks confirm the finite computations; they neither prove all
depths nor constitute Lean kernel verification.

## Decision at the end of session five

Established:

- The initial conjecture is disproved.
- Quotient criterion Q is proved and compared with the literature.
- The construction $D_{n,m}$ is defined and its properties proved.
- $r_1=3$ is computed by hand and the general upper bound (23) is proved.
- For $m=0,1,2,3$, the ranks are $2,3,5,9$.

Session five ends with the exact conjecture:

> **B1-R, conjecture after session five.** For the biset (3) over the free
> group $F(a,b)$, prove $r_m=2^m+1$ for every $m\ge0$.

The upper bound is already available at this stage. Next, construct for
each $m$ enough elements of $H_m$ with $2^m+1$ linearly independent
portraits, or find a mechanism disproving equality. The check must account
for transitions between levels and the distinction between the free group
and the faithful action group.

**Status after session five:** four depths checked; the general case
unproved; novelty unestablished.
**Current status:** the general equality is proved in the audit;
B1-R is no longer the primary research candidate.

Screening plan after session five:

- Compare the computed group with abelianizations of Basilica-group stabilizers.
- Check whether the known recursion-image description immediately supplies
  the lower bound.
- Determine how nilpotent quotient algorithms apply to its $L$-presentations.
- If the abelian case is entirely known, check whether the next layer
  $\gamma_3$ retains a substantive question.

If the formula is a standard consequence, write the exact reduction and
choose a refinement. A question about the next layer must pass the same
initial screening.

# What to reproduce independently

Start from a blank page when reproducing this example.
One action per session is enough:

1. Derive (1) and the inverse-section formula from the biset axioms.
2. Compute (4) by hand without using the completed commutator table.
3. Prove both directions of criterion Q.
4. Check (16), then independently choose a nonzero minor in (17).
5. Recover (25) at $m=2$ on four leaves; write the three orthogonal
   rows and explain $r_2\le5$.

For each attempt, record the last correct step and where it stops.
Assign reading after identifying a specific gap: wreath products,
normal subgroups, abelianization, Schreier rewriting, or integer matrix rank.

Suitable first formalization targets are the section product formula,
criterion Q, computation (4) and its abelian images, the kernel in (13),
and independence of the three vectors (17).
This document does not claim completed Lean code for those new statements.

# Sources and verification status

1. Bartholdi–Dudko, *Algorithmic aspects of branched coverings I*,
   [arXiv:1512.08539](https://arxiv.org/abs/1512.08539).
   Definitions of left-free biset, basis, wreath map, and basis change
   from §2; local source **bc1-bisets.tex**.
2. Nekrashevych, early version of *Self-similar groups*,
   [PDF](https://www.math.stonybrook.edu/~mlyubich/Archive/Stock/Nekrash.pdf),
   §2.7.3, Proposition 2.7.4, pp. 40–41.
   The statement and relevant criterion argument were checked.
3. Benli–Grigorchuk–de la Harpe, *Amenable groups without finitely presented
   amenable covers*,
   [Example 2.17](https://link.springer.com/article/10.1007/s13373-013-0031-5).
   The recursion and the distinction between the free cover and faithful
   action group were checked.
4. Eick–Hartung–Bartholdi, *A nilpotent quotient algorithm for L-presented groups*,
   [arXiv:0706.3131v2](https://arxiv.org/abs/0706.3131v2).
   Only bibliographic information and the abstract have been checked.
   The algorithm has not yet been matched precisely with $D_{n,m}$.
5. Miller–Steinberg, *Homology and K-theory for self-similar actions of groups
   and groupoids*,
   [arXiv:2409.02359v3](https://arxiv.org/abs/2409.02359v3).
   Only the abstract has been checked: it uses a transfer map and virtual
   endomorphism. The precise identification of (19) remains to be made.
6. Di Domenico–Fernández-Alcober–Noce–Thillaisundaram, *p-Basilica Groups*,
   [2022 paper](https://link.springer.com/article/10.1007/s00009-022-02187-z).
   The introduction and Theorem A contain closely related abelian and
   commutator quotient calculations. The later analysis of Lemma 3.2,
   Theorems 3.3 and 4.1 appears in a separate audit; the exact published
   location of our formula has not been identified.
7. Bartholdi–Dudko–Pilgrim, *Correspondences on Riemann surfaces and
   non-uniform hyperbolicity*,
   [arXiv:2407.15548v2](https://arxiv.org/abs/2407.15548v2),
   version of 15 October 2025.
   The abstract explicitly uses a biset description of pullback contraction.
   It provides current context; its main theorems are not used in this example.

Information checked on 6 November 2026.
No external mathematical review of this worked example has been received.