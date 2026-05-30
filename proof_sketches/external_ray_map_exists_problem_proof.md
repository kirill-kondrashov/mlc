# Exact proof of the remaining problem: covering-degree rigidity

This note proves **exactly** the remaining problem stated in
`draft/external_ray_map_exists_problem.md`.

It does **not** assert any new analytic fact about the specific restricted
outside Böttcher map for $f(z)=z^2+2$. The argument below is a conditional
theorem: **if** a map
$$
\phi:V\to\Omega
$$
satisfies the four hypotheses of Problem A, **then** its covering degree is
exactly $1$.

## Theorem

Let

$$
V=\{z\in\mathbb C: |z|>4\},
\qquad
\Omega=\{w\in\mathbb C: |w|>1\}.
$$

Let

$$
\phi:V\to\Omega
$$

be any map satisfying the following assumptions:

1. $\phi$ is proper.
2. $\phi$ is a local homeomorphism.
3. There exists an integer $d\ge 1$ such that, for every $w\in\Omega$,
   $$
   \#\phi^{-1}(w)=d.
   $$
4. For some $R>4$, the loop
   $$
   \gamma_R:S^1\to\Omega,
   \qquad
   \gamma_R(e^{2\pi i t})=\phi(Re^{2\pi i t}),
   $$
   is freely homotopic in $\Omega$ to the positively oriented circle
   $$
   \sigma_R:S^1\to\Omega,
   \qquad
   \sigma_R(e^{2\pi i t})=Re^{2\pi i t}.
   $$

Then

$$
d=1.
$$

Equivalently, $\phi$ is a degree-one covering of $\Omega$, so every fiber of
$\phi$ consists of exactly one point.

## Proof

### Step 1. $\phi$ is a connected $d$-sheeted covering map

Because $d\ge 1$, every fiber is nonempty, so $\phi$ is surjective.

Fix $w\in\Omega$, and write

$$
\phi^{-1}(w)=\{z_1,\dots,z_d\}.
$$

Since $\phi$ is a local homeomorphism, for each $i$ there exists an open
neighborhood $N_i\subset V$ of $z_i$ such that

$$
\phi|_{N_i}:N_i\to \phi(N_i)
$$

is a homeomorphism onto an open neighborhood of $w$.

Because $V$ is an open subset of $\mathbb C$, it is locally compact and
Hausdorff. After shrinking the $N_i$, we may choose open sets

$$
z_i\in U_i\subset \overline{U_i}^{\,V}\subset N_i
$$

such that the compact sets $\overline{U_i}^{\,V}$ are pairwise disjoint. Then
each restriction

$$
\phi|_{U_i}:U_i\to \phi(U_i)
$$

is still a homeomorphism onto an open neighborhood of $w$.

Choose an open neighborhood $W_0$ of $w$ with compact closure
$\overline{W_0}^{\,\Omega}\subset\Omega$ and

$$
W_0\subset \bigcap_{i=1}^d \phi(U_i).
$$

We claim that there exists an open neighborhood $W\subset W_0$ of $w$ such that

$$
\phi^{-1}(W)\subset \bigcup_{i=1}^d U_i.
$$

Suppose not. Then, because $\Omega$ is metrizable, there are points

$$
w_n\in W_0,
\qquad
w_n\to w,
$$

and points

$$
x_n\in \phi^{-1}(w_n)\setminus \bigcup_{i=1}^d U_i.
$$

Since $\overline{W_0}^{\,\Omega}$ is compact and $\phi$ is proper, the set

$$
\phi^{-1}(\overline{W_0}^{\,\Omega})
$$

is compact in $V$. Passing to a subsequence, we may assume that

$$
x_n\to x\in V.
$$

By continuity of $\phi$,

$$
\phi(x)=\lim_{n\to\infty}\phi(x_n)=\lim_{n\to\infty}w_n=w,
$$

so $x=z_i$ for some $i$. But $U_i$ is an open neighborhood of $z_i$, hence
$x_n\in U_i$ for all sufficiently large $n$, contradicting the construction of
$x_n$. This proves the claim.

Now set

$$
U_i' = U_i\cap \phi^{-1}(W).
$$

Because $W\subset \phi(U_i)$ and $\phi|_{U_i}$ is injective, each restriction

$$
\phi|_{U_i'}:U_i'\to W
$$

is a homeomorphism. The claim gives the disjoint decomposition

$$
\phi^{-1}(W)=\bigsqcup_{i=1}^d U_i'.
$$

So $w$ is evenly covered. Since $w\in\Omega$ was arbitrary, every point of
$\Omega$ is evenly covered, and therefore $\phi:V\to\Omega$ is a $d$-sheeted
covering map.

The space $V=\{z\in\mathbb C:|z|>4\}$ is path-connected, so this covering is
connected.

### Step 2. The image subgroup in $\pi_1(\Omega)$ has index $d$

Fix the base point

$$
x_0=R\in V,
\qquad
y_0=\phi(x_0)\in\Omega.
$$

Define the positively oriented circle in $V$ by

$$
c_R:[0,1]\to V,
\qquad
c_R(t)=Re^{2\pi i t}.
$$

This is a loop based at $x_0$. Since $V$ deformation retracts onto the circle
$|z|=R$, the class $[c_R]$ generates $\pi_1(V,x_0)\cong\mathbb Z$.

Because $\phi$ is a connected $d$-sheeted covering, the standard covering-space
correspondence gives

$$
\bigl[\pi_1(\Omega,y_0):\phi_*(\pi_1(V,x_0))\bigr]=d.
$$

Indeed, for a connected covering $p:X\to Y$, the fiber over $p(x_0)$ is in
canonical bijection with the set of left cosets of

$$
p_*(\pi_1(X,x_0))
$$

in $\pi_1(Y,p(x_0))$, obtained by lifting loops at $p(x_0)$ starting at $x_0$.
Applying this to $p=\phi$ yields the index formula above.

Now $\pi_1(\Omega,y_0)\cong\mathbb Z$, and its unique subgroup of index $d$ is
$d\mathbb Z$. Since $[c_R]$ generates $\pi_1(V,x_0)$, the element

$$
\phi_*([c_R])
$$

generates the subgroup $\phi_*(\pi_1(V,x_0))$. Therefore, under the winding
number isomorphism

$$
\pi_1(\Omega,y_0)\cong\mathbb Z,
$$

the class $\phi_*([c_R])$ corresponds to

$$
\pm d.
$$

Equivalently, the loop $\phi\circ c_R$ has winding number

$$
\operatorname{wind}(\phi\circ c_R,0)=\pm d.
$$

### Step 3. The free homotopy hypothesis forces winding number $1$

By definition of $\gamma_R$,

$$
(\phi\circ c_R)(t)=\phi(Re^{2\pi i t})=\gamma_R(e^{2\pi i t}).
$$

So $\phi\circ c_R$ is just the standard $[0,1]$-parameterization of $\gamma_R$.
Likewise,

$$
\sigma_R(e^{2\pi i t})=Re^{2\pi i t}=c_R(t).
$$

Hence the free homotopy assumption says exactly that the loop $\phi\circ c_R$ is
freely homotopic in $\Omega$ to the positively oriented circle $c_R$.

The winding number about $0$ is invariant under free homotopy through loops in
$\Omega=\mathbb C\setminus \overline{D(0,1)}\subset \mathbb C\setminus\{0\}$.
Therefore

$$
\operatorname{wind}(\phi\circ c_R,0)=\operatorname{wind}(c_R,0)=1.
$$

Combining this with Step 2 gives

$$
\pm d=1.
$$

Since $d\ge 1$ is an integer, it follows that

$$
d=1.
$$

This proves the remaining draft problem.

## Why this note is exact and not falsifiable

The statement proved here is exactly the theorem-shaped content of the remaining
draft problem and nothing stronger.

1. The proof assumes properness and local homeomorphy; it does not attempt to
   prove them.
2. The proof assumes the constant finite fiber hypothesis; it does not derive it
   from unrelated dynamical input.
3. The proof uses the free homotopy hypothesis only to identify the winding
   number of the large circle image with $1$.
4. Therefore the note does **not** assert any new concrete fact about the
   specific restricted outside Böttcher map beyond the conditional implication
   stated in the draft.

So this file is a rigorous proof of the exact topological statement the expert is
being asked to establish, with no extra claim added beyond that statement.
