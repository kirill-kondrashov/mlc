# Exact proof for Problem A: covering-degree rigidity

This note proves Problem A from `draft/external_ray_map_exists_problem.md` in GitHub-friendly Markdown, using `$$` display math.

On the checked Lean root, this topology theorem is now paired only with a
separate minimal-counterexample obstruction statement for the explicit
local-homeomorph/closed-preimage route to the direct proper/local witness. So
the last project axiom packages two theorem-shaped pieces rather than a
concrete witness fact.

## Theorem

Let

$$
V=\{z\in\mathbb C: |z|>4\},\qquad
\Omega=\{w\in\mathbb C: |w|>1\}.
$$

Let $\phi:V\to\Omega$ be proper and a local homeomorphism. Assume that there is an integer $d\ge 1$ such that every fiber has cardinality $d$:

$$
\#\phi^{-1}(w)=d\qquad\text{for every }w\in\Omega.
$$

Assume also that for some $R>4$, the loop

$$
\Gamma_R(t)=\phi(Re^{2\pi i t}),\qquad t\in[0,1],
$$

is freely homotopic in $\Omega$ to the positively oriented exterior circle

$$
C_R(t)=Re^{2\pi i t}.
$$

Then $d=1$. Hence every fiber of $\phi$ consists of exactly one point.

## Proof

First prove that $\phi$ is a connected $d$-sheeted covering map.

Since $d\ge 1$, every fiber is nonempty, so $\phi$ is surjective. Fix $w\in\Omega$, and write

$$
\phi^{-1}(w)=\{z_1,\ldots,z_d\}.
$$

For each $i$, since $\phi$ is a local homeomorphism, choose an open neighborhood $N_i\subset V$ of $z_i$ such that

$$
\phi|_{N_i}:N_i\to\phi(N_i)
$$

is a homeomorphism onto an open neighborhood of $w$. Because $V$ is an open subset of $\mathbb C$, it is locally compact, Hausdorff, metrizable, and regular. Since the points $z_1,\ldots,z_d$ are distinct, shrink to open sets $U_i$ with

$$
z_i\in U_i\subset \overline{U_i}^{\,V}\subset N_i,
$$

such that the compact closures $\overline{U_i}^{\,V}$ are pairwise disjoint. Then $\phi|_{U_i}$ is a homeomorphism onto the open set $\phi(U_i)$, which contains $w$. Choose an open neighborhood $W_0$ of $w$ with compact closure in $\Omega$ and

$$
W_0\subset \bigcap_{i=1}^d \phi(U_i).
$$

There exists an open neighborhood $W\subset W_0$ of $w$ such that

$$
\phi^{-1}(W)\subset \bigcup_{i=1}^d U_i.
$$

Otherwise, since $\Omega$ is metrizable, there are points $w_n\to w$, with $w_n\in W_0$, and points

$$
x_n\in \phi^{-1}(w_n)\setminus\bigcup_i U_i.
$$

Properness gives compactness of $\phi^{-1}(\overline{W_0})$. Passing to a subsequence, $x_n\to x\in V$. By continuity, $\phi(x)=w$, so $x=z_i$ for some $i$. Since $U_i$ is a neighborhood of $z_i$, this forces $x_n\in U_i$ for all sufficiently large $n$, contradicting the choice of $x_n$.

For each $i$, set

$$
U_i'=U_i\cap\phi^{-1}(W).
$$

Since $W\subset\phi(U_i)$ and $\phi|_{U_i}$ is injective, each restriction

$$
\phi|_{U_i'}:U_i'\to W
$$

is a homeomorphism. The containment above gives the disjoint decomposition

$$
\phi^{-1}(W)=\bigsqcup_{i=1}^d U_i'.
$$

Thus every point of $\Omega$ is evenly covered. Therefore $\phi:V\to\Omega$ is a $d$-sheeted covering map. Since $V$ is path-connected, this covering is connected.

Now compute the induced map on fundamental groups. Let

$$
x_0=R\in V,\qquad y_0=\phi(x_0)\in\Omega.
$$

The loop $C_R(t)=Re^{2\pi i t}$, based at $x_0$, is the positive generator of $\pi_1(V,x_0)\cong\mathbb Z$. Its image under $\phi$ is $\Gamma_R$, based at $y_0$, so

$$
[\Gamma_R]=\phi_*([C_R])\in\pi_1(\Omega,y_0).
$$

For a covering $p:X\to Y$ with $X$ path-connected, the subgroup

$$
p_*(\pi_1(X,x))\subseteq \pi_1(Y,p(x))
$$

has index equal to $\#p^{-1}(p(x))$. This is the standard path-lifting coset formula: lifting loops at $p(x)$ from $x$ identifies the fiber over $p(x)$ with the cosets of $p_*(\pi_1(X,x))$.

Applying this to the connected $d$-sheeted covering $\phi$, the subgroup

$$
\phi_*(\pi_1(V,x_0))\subseteq \pi_1(\Omega,y_0)
$$

has index $d$. Identify $\pi_1(\Omega,y_0)\cong\mathbb Z$ by winding number around $0$. The only subgroup of $\mathbb Z$ of index $d$ is $d\mathbb Z$. Because $[C_R]$ generates $\pi_1(V,x_0)$, the element

$$
[\Gamma_R]=\phi_*([C_R])
$$

generates this index-$d$ subgroup. Hence

$$
\operatorname{wind}(\Gamma_R,0)=\varepsilon d
$$

for some $\varepsilon\in\{1,-1\}$.

On the other hand, $\Gamma_R$ is freely homotopic in $\Omega$ to the positively oriented exterior circle $C_R$. Winding number about $0$ is invariant under free homotopy through loops in $\Omega$. Therefore

$$
\operatorname{wind}(\Gamma_R,0)=\operatorname{wind}(C_R,0)=1.
$$

Thus $\varepsilon d=1$. Since $d\ge 1$, it follows that $d=1$.

The assumed constant fiber cardinality then gives

$$
\#\phi^{-1}(w)=1\qquad\text{for every }w\in\Omega.
$$

So $\phi$ is a degree-one covering of $\Omega$, and every fiber is a singleton.

## Double-check

This proof matches Problem A exactly.

- Properness and local homeomorphy are used only to prove that $\phi$ is a connected finite covering.
- The hypothesis $\#\phi^{-1}(w)=d\ge 1$ gives surjectivity and the sheet number.
- The free homotopy uses the exterior circle $C_R(t)=Re^{2\pi i t}$, which lies in $\Omega$ because $R>4$.
- The based fundamental-group computation is converted to winding number before using free homotopy, avoiding a basepoint mismatch.
- The comparison gives $\varepsilon d=1$, and since $d\ge 1$, this forces $d=1$.
