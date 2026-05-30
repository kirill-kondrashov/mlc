# Problem B cannot be proved as stated

This note records why the previous route-level formulation of Problem B was
eliminated from the live frontier.

The conclusion is:

1. the local-homeomorphism clause is true;
2. the compactness clause is false as written.

So there is no honest rigorous proof of that earlier route statement.

## Setup

Let

$$
f(z)=z^2+2.
$$

Let

$$
U_\infty=\{z\in\mathbb C:f^{\circ n}(z)\to\infty\}
$$

be the basin of infinity. The classical Böttcher theorem gives a biholomorphism

$$
\Phi:U_\infty\to\{w\in\mathbb C:\lvert w\rvert>1\}
$$

such that

$$
\Phi(f(z))=\Phi(z)^2
$$

and

$$
\frac{\Phi(z)}{z}\to 1
\qquad
\text{as }
\qquad
z\to\infty.
$$

The map in the draft is the restriction

$$
\phi=\Phi|_V,
\qquad
V=\{z\in\mathbb C:\lvert z\rvert>4\}.
$$

## Part 1. The map above is a local homeomorphism

If

$$
\lvert z\rvert>2,
$$

then

$$
\lvert f(z)\rvert=\lvert z^2+2\rvert\ge \lvert z\rvert^2-2>\lvert z\rvert,
$$

so every point with

$$
\lvert z\rvert>2
$$

belongs to

$$
U_\infty.
$$

In particular,

$$
V\subset U_\infty.
$$

Since

$$
\Phi
$$

is biholomorphic on

$$
U_\infty,
$$

its derivative never vanishes there. By the complex inverse function theorem,

$$
\Phi
$$

is a local biholomorphism at every point of

$$
U_\infty.
$$

Restricting to

$$
V
$$

shows that

$$
\phi:V\to\{w\in\mathbb C:\lvert w\rvert>1\}
$$

is a local homeomorphism.

Thus the first clause of Problem B is correct.

## Part 2. The compactness clause is false

Consider the boundary point

$$
z_\ast=4.
$$

Since

$$
\lvert z_\ast\rvert=4>2,
$$

we have

$$
z_\ast\in U_\infty,
$$

so

$$
\Phi
$$

is holomorphic, hence continuous, at

$$
z_\ast.
$$

For each integer

$$
n\ge 1,
$$

set

$$
z_n=4+\frac1n.
$$

Then

$$
z_n\in V
$$

and

$$
z_n\to z_\ast.
$$

Define

$$
w_n=\Phi(z_n),
\qquad
w_\ast=\Phi(z_\ast).
$$

By continuity of

$$
\Phi,
$$

we have

$$
w_n\to w_\ast.
$$

Moreover,

$$
w_\ast\in\{w\in\mathbb C:\lvert w\rvert>1\},
$$

because

$$
\Phi
$$

maps

$$
U_\infty
$$

to the exterior of the unit disk.

Now define

$$
K=\{w_\ast\}\cup\{w_n:n\ge 1\}.
$$

This set is compact in

$$
\Omega=\{w\in\mathbb C:\lvert w\rvert>1\},
$$

because it is a convergent sequence together with its limit.

Let

$$
E_K=\{z\in\mathbb C:\lvert z\rvert>4\text{ and }\phi(z)\in K\}.
$$

For every integer

$$
n\ge 1,
$$

we have

$$
z_n\in E_K,
$$

because

$$
\phi(z_n)=\Phi(z_n)=w_n\in K.
$$

Hence

$$
z_\ast=4
$$

belongs to the closure of

$$
E_K
$$

in

$$
\mathbb C.
$$

But

$$
4\notin E_K,
$$

because the defining condition

$$
\lvert z\rvert>4
$$

fails at

$$
z=4.
$$

Therefore

$$
E_K
$$

is not closed in

$$
\mathbb C.
$$

Since

$$
\mathbb C
$$

is Hausdorff, every compact subset of

$$
\mathbb C
$$

is closed. We have just proved that

$$
E_K
$$

is not closed in

$$
\mathbb C.
$$

Therefore

$$
E_K
$$

is not compact in

$$
\mathbb C.
$$

This disproves the second clause of Problem B.

## Conclusion

The earlier route statement was false. Its first clause is true, but its second
clause admits the explicit counterexample constructed above. Accordingly, the
live remaining route-side frontier has been reduced to the direct proper/local
witness statement in `draft/restricted_map_route_problem.md`.
