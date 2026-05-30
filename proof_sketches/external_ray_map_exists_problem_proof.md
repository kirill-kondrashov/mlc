# Exact proof of Problem A: monodromy rigidity of the covering degree

This note proves exactly the statement in
`draft/external_ray_map_exists_problem.md`.

## Theorem

Let

$$
V=\{z\in\mathbb C:\lvert z\rvert>4\},
\qquad
\Omega=\{w\in\mathbb C:\lvert w\rvert>1\},
$$

and let

$$
\phi:V\to\Omega
$$

be any map satisfying the following assumptions:

1. The map above is a local homeomorphism.
2. There exists an integer
   $$
   d\ge 1
   $$
   such that, for every point
   $$
   w\in\Omega,
   $$
   $$
   \#\phi^{-1}(w)=d.
   $$
3. For some number
   $$
   R>4,
   $$
   the loop
   $$
   \gamma_R:S^1\to\Omega,
   \qquad
   \gamma_R(e^{2\pi i t})=\phi(Re^{2\pi i t}),
   $$
   is freely homotopic through loops in the exterior domain to the positively
   oriented circle
   $$
   \sigma_R:S^1\to\Omega,
   \qquad
   \sigma_R(e^{2\pi i t})=Re^{2\pi i t}.
   $$

Then

$$
d=1.
$$

## Proof

### Step 1. The map above is a connected covering of degree $$d$$

Fix a point

$$
w\in\Omega.
$$

By assumption,

$$
\phi^{-1}(w)=\{z_1,\dots,z_d\}.
$$

Since the map above is a local homeomorphism, for each index

$$
i\in\{1,\dots,d\}
$$

there exists an open neighborhood

$$
N_i\subset V
$$

of

$$
z_i
$$

such that

$$
\phi|_{N_i}:N_i\to \phi(N_i)
$$

is a homeomorphism onto an open neighborhood of

$$
w.
$$

Because

$$
z_1,\dots,z_d
$$

are finitely many distinct points in the Hausdorff space

$$
V,
$$

we may shrink the sets

$$
N_i
$$

so that they are pairwise disjoint. Set

$$
W=\bigcap_{i=1}^d \phi(N_i).
$$

Then

$$
W
$$

is an open neighborhood of

$$
w.
$$

For each index

$$
i,
$$

let

$$
U_i=N_i\cap \phi^{-1}(W).
$$

Then

$$
\phi|_{U_i}:U_i\to W
$$

is a homeomorphism, so every point of

$$
W
$$

has at least one preimage in each

$$
U_i.
$$

Now fix any point

$$
y\in W.
$$

The sets

$$
U_1,\dots,U_d
$$

are pairwise disjoint, and each of them contains exactly one point of

$$
\phi^{-1}(y).
$$

Hence

$$
\phi^{-1}(y)
$$

contains at least

$$
d
$$

points. By the constant-fiber hypothesis it contains exactly

$$
d
$$

points, so these are all the preimages. Therefore

$$
\phi^{-1}(W)=\bigsqcup_{i=1}^d U_i,
$$

and every restriction

$$
\phi|_{U_i}:U_i\to W
$$

is a homeomorphism.

Thus every point of

$$
\Omega
$$

is evenly covered, so the map above is a covering map of degree

$$
d.
$$

The domain

$$
V=\{z\in\mathbb C:\lvert z\rvert>4\}
$$

is path-connected, so this covering is connected.

### Step 2. The induced subgroup has index $$d$$

Fix the base point

$$
x_0=R\in V.
$$

Let

$$
c_R:[0,1]\to V,
\qquad
c_R(t)=Re^{2\pi i t}.
$$

Since

$$
V
$$

deformation retracts onto the circle

$$
\{z\in\mathbb C:\lvert z\rvert=R\},
$$

the class of

$$
c_R
$$

generates

$$
\pi_1(V,x_0)\cong\mathbb Z.
$$

For a connected covering of degree

$$
d,
$$

the image subgroup

$$
\phi_*\bigl(\pi_1(V,x_0)\bigr)
$$

has index

$$
d
$$

in

$$
\pi_1(\Omega,\phi(x_0)).
$$

Since

$$
\Omega=\{w\in\mathbb C:\lvert w\rvert>1\}
$$

is also homotopy equivalent to a circle, we have

$$
\pi_1(\Omega,\phi(x_0))\cong\mathbb Z.
$$

The only subgroup of index

$$
d
$$

in

$$
\mathbb Z
$$

is

$$
d\mathbb Z.
$$

Therefore the element

$$
\phi_*([c_R])
$$

corresponds, under the winding-number identification, to

$$
\pm d.
$$

Equivalently, the loop

$$
\phi\circ c_R
$$

has winding number

$$
\operatorname{wind}(\phi\circ c_R,0)=\pm d.
$$

### Step 3. The free homotopy forces winding number $$1$$

By definition,

$$
(\phi\circ c_R)(t)=\phi(Re^{2\pi i t})=\gamma_R(e^{2\pi i t}).
$$

Thus

$$
\phi\circ c_R
$$

is the standard parametrization of the loop

$$
\gamma_R.
$$

Likewise,

$$
\sigma_R(e^{2\pi i t})=Re^{2\pi i t}=c_R(t),
$$

so

$$
\sigma_R
$$

is the same geometric loop as

$$
c_R.
$$

The free homotopy hypothesis therefore says that

$$
\phi\circ c_R
$$

is freely homotopic in

$$
\Omega
$$

to the positively oriented circle

$$
c_R.
$$

Winding number about the origin is invariant under free homotopy through loops
in

$$
\mathbb C\setminus\{0\}.
$$

Since

$$
\Omega\subset \mathbb C\setminus\{0\},
$$

we obtain

$$
\operatorname{wind}(\phi\circ c_R,0)=\operatorname{wind}(c_R,0)=1.
$$

Combining this with Step 2 yields

$$
\pm d=1.
$$

Because

$$
d\ge 1
$$

is an integer, it follows that

$$
d=1.
$$

This is exactly the conclusion of Problem A.
