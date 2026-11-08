# B3: global curve attractor for the rabbit–Basilica mating

**Status on 8 November 2026:** the Pilgrim direction, in the separate
`pilgrim-bisets` package. The main B3 theorem is unproved; no implication
to MLC is established. The mathematical audit of 7 November is preserved below.

7 November 2026. **The full theorem passed literature screening;
the next stage is a two-week feasibility check of the method.**

[Targeted publication-novelty screening](B3_publication_screening.md),
[PDF](../b3_publication.pdf): the paper goal is an explicit attractor
and a proof for every curve. Isolated calculations do not constitute this goal.

**Post-audit update:** Pilgrim's criterion has been checked and does not
apply: $\rho(\varphi_F)\ge1$. An essential preimage of a curve is unique
when it exists. The complete proof and remaining step are in the
[audit](B3_novelty_audit.md), [PDF](../b3_audit.pdf).
The goal is an explicit finite global attractor and eventual entry for
every curve, for one map with five postcritical points.
The main statement remains unproved. The comparison below excludes
direct applications of several related theorems, including to iterates.

## 1. Candidate selection

Three possibilities were checked.

1. **Continue with $H_m/D_{4,m}$ for Basilica.**
   The free and faithful groups genuinely differ here.
   No dynamical question answered by this computation has been identified.
   Retained as a reserve; no research cycle begins on it.
2. **Finite curve attractors with four postcritical points.**
   Existence is already proved by Bartholdi–Dudko–Pilgrim, Corollary B.
   The candidate is closed at this level of generality.
3. **An explicit attractor for a particular five-point map.**
   Choose $F$ below. The checked results supply neither a ready list of
   curves nor a proof of global attraction for it.

Working title: **"A biset certificate for the global curve attractor
of the rabbit–Basilica mating."**

## 2. Object and proposed theorem

Let

$$
\lambda=\frac{1+i\sqrt3}{2},\qquad \lambda^2-\lambda+1=0,
\qquad F(z)=\frac{z^2+\lambda}{z^2-1}.
\tag{C1}
$$

This map is known. Bonnot–Braverman–Yampolsky,
[*Thurston equivalence to a rational map is decidable*](https://arxiv.org/abs/1009.5713v1),
§2, preprint pp. 3–4, describe it as the rabbit–Basilica mating.
They also give an invariant curve with multiplier $1/2$.
Neither existence of the map nor discovery of that one curve is part
of the proposed contribution.

Write

$$
P=\{0,-\lambda,1-\lambda,\infty,1\},
\qquad \mathcal C=\mathcal C(S^2,P).
$$

Here $\mathcal C$ consists of unoriented essential simple closed curves
up to isotopy relative to $P$. Essential means that each side contains
at least two points of $P$.
For $\gamma\in\mathcal C$, let $\mathcal P_F(\gamma)$ be the set of
essential classes of components of $F^{-1}(\gamma)$, counting coincident
classes once. For sets, take the union of their images.

**Proposed theorem B3.** Explicitly exhibit a finite
$\mathcal A\subset\mathcal C$ in fixed curve coordinates and prove

$$
\mathcal P_F(\mathcal A)\subseteq\mathcal A,
\qquad
\forall\gamma\in\mathcal C\ \exists N(\gamma)\quad
\forall n\ge N(\gamma):\quad
\mathcal P_F^{\,n}(\gamma)\subseteq\mathcal A.
\tag{C2}
$$

Supply the complete transition table inside $\mathcal A$ and a checkable
argument for an arbitrary initial curve. The entry time $N$ depends on
the curve. Minimality and convergence-rate bounds are outside the initial task.

The general statement controls every essential component.
For this map, the audit proves that there is at most one, giving a
partial function on curve classes.

## 3. Initial analysis: completed calculations

From (C1),

$$
0\longmapsto-\lambda\longmapsto1-\lambda\longmapsto0,
\qquad
\infty\longmapsto1\longmapsto\infty.
\tag{C3}
$$

In the finite plane, $F'(z)=-2(1+\lambda)z/(z^2-1)^2$;
the poles $\pm1$ are simple. In the coordinate $w=1/z$,
$F(1/w)=1+(1+\lambda)w^2+O(w^4)$.
Thus the critical points are exactly $0,\infty$, each of local degree $2$,
and the postcritical set is $P$. The explicit value of $\lambda$ shows
that the five points are pairwise distinct.

Complete fibers above $P$:

| $y$ | $F^{-1}(y)$ | Multiplicities |
| --- | --- | --- |
| $0$ | $1-\lambda,\lambda-1$ | $1,1$ |
| $-\lambda$ | $0$ | $2$ |
| $1-\lambda$ | $-\lambda,\lambda$ | $1,1$ |
| $\infty$ | $1,-1$ | $1,1$ |
| $1$ | $\infty$ | $2$ |

Therefore,

$$
Q=F^{-1}(P)=P\sqcup\{\lambda-1,\lambda,-1\}.
\tag{C4}
$$

The biset comes from the correspondence

$$
S^2-P\ \xleftarrow{\ F\ }\ S^2-Q\
\xrightarrow{\ \iota\ }\ S^2-P.
\tag{C5}
$$

The first arrow is an unbranched degree-$2$ covering; the second fills
three extra punctures. Thus the biset group is
$G=\pi_1(S^2-P)\simeq F_4$, and the biset has rank $2$.
The middle space has fundamental group of rank $7$;
Euler characteristic checks as $2-8=2(2-5)$.

The fiber table determines puncture monodromy permutations:
transpositions occur exactly above $-\lambda$ and $1$.
It does not determine section words; connecting paths must be chosen and traced.

### Why the nearest general theorems do not settle this case

**Four points.** Corollary B of
[Bartholdi–Dudko–Pilgrim, version 2](https://arxiv.org/abs/2407.15548v2),
§1.1, assumes $\#P=4$, whereas here $\#P=5$.
Moreover, $F|_P$ has cycles of lengths $3$ and $2$, so $P$ has no
four-point invariant subset.
For every $n\ge1$, the postcritical set of $F^n$ is also $P$.
Indeed, its critical values contain $F(C_F),\ldots,F^n(C_F)$;
further iterations of $F^n$ give every positive power of $F$ on $C_F$.
The reverse inclusion is immediate.

**Polynomials and gluing two polynomials.** Check every iterate as well.
If $x$ is fixed by $F^n$ and its orbit avoids critical points of $F$,
then $\deg_xF^n=1$. Otherwise $x$ lies in one of the cycles (C3).
By multiplicativity of local degrees, the largest local degree at a
fixed point is

$$
M_n=\max\Bigl(\{1\}
\cup\{2^{n/2}:2\mid n\}
\cup\{2^{n/3}:3\mid n\}\Bigr)
\le 2^{\lfloor n/2\rfloor}.
\tag{C6}
$$

A degree-$2^n$ polynomial fixes $\infty$ with local degree $2^n>M_n$.
Hence no $F^n$ is conjugate to a polynomial.

In Wu,
[*On the Global Curve Attractor for polynomial gluing*, version 2](https://arxiv.org/abs/2605.00633v2),
§§1.1, 2.2–2.3, gluing polynomials of degrees $d_1,d_2$ along finite
immediate basins gives degree $D=d_1+d_2-d_0$, $d_0\ge2$.
Two distinct fixed points survive: the original infinities, of local
degrees $d_1,d_2$. If such a gluing gave $F^n$, then $d_1,d_2\le M_n$, so

$$
2^n=D=d_1+d_2-d_0\le2M_n-2
\le2^{\lfloor n/2\rfloor+1}-2<2^n,
$$

a contradiction. Thus Wu's result does not apply to $F$ or any iterate
through this gluing of two polynomials. The argument is independent of
the condition on the remaining critical orbits weakened in version 2.

**Critically fixed maps.** The critical points of $F$ are not fixed.
For $n\ge2$, $x=\lambda-1\notin P$ is critical for $F^n$, since $F(x)=0$,
but $F^n(x)\in P$, so it is not fixed. The critically fixed theorem
therefore does not apply to iterates either.

These checks exclude the listed direct reductions. They do not exclude
other criteria, particularly the mapping-class virtual endomorphism criterion.

## 4. Pilgrim's criterion: audit complete

The [detailed audit](B3_novelty_audit.md) computes the moduli correspondence
and proves surjectivity of the virtual endomorphism and $\rho(\varphi_F)\ge1$.
It also constructs an obstructed member of the same Hurwitz class.
Thus the whole biset is not strongly contracting;
Pilgrim's Theorem 1.4 does not reduce B3 to a known result.

For $F$ itself, arbitrarily long finite degree-one pullback chains
preserving the partition $\{a_1,b_1\}$ have been constructed.
This excludes a height depending only on puncture partitions, even with
fixed pullback blocks. The main attractor statement remains unproved.

The Bonnot–Braverman–Yampolsky equator must still belong to every attractor
in (C2): it pulls back to the same class with degree $2$.
Specifying the separated punctures alone does not identify its isotopy class.

The proposed additional step is control of isotopy classes and unbounded
twist parameters for the fixed map $F$.

## 5. A concrete computational model

Fix an ideal triangulation with vertices
$p_0=0,p_1=1,p_2=1-\lambda,p_3=-\lambda,p_4=\infty$.
In the finite plane take the quadrilateral boundary $p_0p_1p_2p_3$
and diagonal $p_0p_2$; outside it join the four vertices to $p_4$
by disjoint arcs. The oriented faces are

$$
(0,2,1),\ (0,3,2),\ (4,0,1),\ (4,1,2),\ (4,2,3),\ (4,3,0).
$$

There are $5$ vertices, $9$ edges, and $6$ faces.
The dual spine has rank $9-6+1=4$, consistent with (C5).

Represent curves by normal arcs in the triangles. Nine intersection
numbers determine a normal multicurve: the numbers of arcs joining
sides are $(n_i+n_j-n_k)/2$, and arcs glue in order across a common edge.
Check nonnegativity, parity, connectedness, and essentiality.
Bounding the coordinate sum by $R$ leaves finitely many classes,
with at most $\binom{R+9}{9}$ vectors.
This standard normal form is used as a tool.

For the biset computation choose basepoint $*=2$ and preimages
$\pm\sqrt{2+\lambda}$. Connecting paths and meridians give a recursion
$\psi(g)=(g|_0,g|_1)\sigma_g$ over $F_4$.
If a simple curve is represented by a cyclic word $g$, then for a cycle
$(s_0,\ldots,s_{d-1})$ of $\sigma_g$, the pullback component word is,
up to conjugacy,

$$
(g^d)|_{s_0}=g|_{s_0}\,g|_{s_1}\cdots g|_{s_{d-1}}.
\tag{C7}
$$

The cycle length $d$ is that component's covering degree.
The formula follows by lifting $d$ successive traversals and applying
the section product rule. After filling the three punctures in (C4),
discard trivial and peripheral classes and forget orientation.
For $d=2$, one section $g|_s$ alone is not a closed component word.

## 6. First substantive lemma still to prove

After obtaining the recursion and a trial list $\mathcal A$, seek an
explicit integer height $h:\mathcal C\to\mathbb N$ and $q\ge1$ such
that $h=0$ exactly on $\mathcal A$,
$\mathcal P_F(\mathcal A)\subseteq\mathcal A$, and

$$
\gamma\notin\mathcal A,\quad
\delta\in\mathcal P_F^{\,q}(\gamma)
\quad\Longrightarrow\quad h(\delta)<h(\gamma).
\tag{C8}
$$

No such $h$ has been constructed. The initial approach uses normal
coordinates and twists about the equator, handling small values separately.
A finite set of cases must cover every simple curve; a word-length
cutoff does not achieve this.

Conditions (C8) imply (C2): on every branch of the pullback tree,
a nonnegative integer decreases every $q$ steps until reaching $\mathcal A$.
After $q\,h(\gamma)$ steps, every essential component therefore lies
in $\mathcal A$ and remains there. This is standard reasoning;
the proposed new part is constructing and proving (C8) for (C1).

The difficulty is unbounded twisting and changes of normal form after
pullback. A finite nucleus of the dynamical biset does not settle this
automatically: (C7) lifts $g^d$, and $d$ can grow under iteration.

## 7. Next four sessions

Each session takes about two hours; use the remaining weekly time for
checking and writing. Section 3's calculations are already prepared.

1. **Fix paths and obtain the biset.** Construct meridians for (C5),
   four free generators, and every section word. Check the fifth meridian
   using the peripheral relation, branching, and fiber table. Produce a
   complete recursion with a path diagram to fix conjugating-word choices.
2. **Compute simple-curve pullbacks.** Implement (C7) with normal coordinates;
   find the known equator's word and verify its degree-$2$ transition.
   Then check closure of the first trial curve list, testing the biset's
   correspondence with topology.
3. **Analyze the contraction boundary.** Recover the audit's degree-one
   chains with the same puncture partition. Specify an additional coordinate
   distinguishing their classes that a height must include. This excludes
   the already disproved induction scheme.
4. **Check an unbounded family.** Choose an essential curve $\eta$ crossing
   the equator and compute pullbacks of $T_{\gamma_{\rm eq}}^k(\eta)$
   for arbitrary $k\in\mathbb Z$. Seek the parameter and normal-arc
   transformation rule, then (C8). This tests the method beyond a finite table.

After two weeks, retain the complete recursion, a trial transition graph,
and a proved formula for at least one infinite family.
Close B3 if these data reduce to a known result.
If infinite families remain uncontrolled, restrict the goal to an exact
curve class and reassess its mathematical significance.

## 8. Limits of the novelty check

The cited parts of Bonnot–Braverman–Yampolsky (2010v1), Pilgrim (2012),
Bartholdi–Dudko–Pilgrim (2025v2), and Wu (2026v2) were inspected.
Also read §§3.3, 4.1 of [Pilgrim's 2021 survey](https://arxiv.org/abs/2102.12402v1)
on known mechanisms. Statements and hypotheses of the nearest results
were checked; the auxiliary exclusions in §3 were proved directly.

Searches included "basilica rabbit mating finite attractor", "five postcritical
points curve attractor", "polynomial gluing global curve attractor", and
"basilica rabbit contracting mapping class".
Title searches serve as pointers to primary texts.

Established distinction: (C1) and every iterate lie outside the checked
four-point, polynomial, critically fixed, and Wu two-polynomial gluing classes.
The known equator is separated from the required global statement.
The mapping-class contraction criterion is now excluded by the audit's
proof, accounting for Parry–Pilgrim (2025v1).
The later [targeted screening](B3_publication_screening.md) checks equivalent
map forms, subsequent work, additional general criteria, and Pf4 source code.
It supports novelty of the full proposed theorem within the inspected
literature. The attractor itself has not been computed.

**Decision:** B3 passes screening as an explicit-attractor problem requiring
a proof for every curve. The biset recursion and control of one infinite
family are the next feasibility tests.

## 9. Reproducible initial data

The [script](b3_compute.py) works exactly in $\mathbb Q(\lambda)$ and checks
orbits, fibers with multiplicities, the degrees in (C6) for $1\le n\le12$,
and consistency of the triangulation.
The [reference data](B3_initial_data.json) contain no attractor computation.
Exclusion of all iterates is proved in §3 independently of these finite checks.

~~~bash
python3 packages/pilgrim-bisets/research/b3_compute.py --check
~~~
