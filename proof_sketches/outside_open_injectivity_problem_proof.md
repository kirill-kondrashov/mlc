# Proof of Problem 2: injectivity on the outside-open region at $$c=2$$

Let

$$
f(z)=z^2+2,
$$

let

$$
U_\infty=\{z\in\mathbb C : f^{\circ n}(z)\to\infty \text{ as } n\to\infty\},
\qquad
\Omega=\{w\in\mathbb C : |w|>1\},
\qquad
V=\{z\in\mathbb C : |z|>4\},
$$

and let

$$
\phi:U_\infty\to\Omega
$$

be the exterior coordinate used in the project.

For this coordinate one has the explicit formula

$$
\phi(z)=\frac{z}{|z|}\,e^{G(z)}
$$

for every nonzero

$$
z\in U_\infty,
$$

where

$$
G(z)=G_f(z)
$$

is the Green function of

$$
f(z)=z^2+2.
$$

The previously established Green-function analysis also gives the following fact:
for every unit complex number

$$
\xi\in\mathbb C,
\qquad
|\xi|=1,
$$

the function

$$
r\longmapsto G(r\xi)
$$

is strictly increasing on the interval

$$
(4,\infty).
$$

We prove that

$$
\phi|_V:V\to\Omega
$$

is injective.

## Proof

Take

$$
z_1,z_2\in V
$$

and assume that

$$
\phi(z_1)=\phi(z_2).
$$

Write

$$
z_j=r_j\xi_j,
\qquad
r_j=|z_j|>4,
\qquad
|\xi_j|=1
$$

for

$$
j=1,2.
$$

Using the explicit formula for

$$
\phi,
$$

we obtain

$$
\xi_1 e^{G(r_1\xi_1)}=\phi(z_1)=\phi(z_2)=\xi_2 e^{G(r_2\xi_2)}.
$$

Take absolute values. Since

$$
|\xi_1|=|\xi_2|=1,
$$

we get

$$
e^{G(r_1\xi_1)}=e^{G(r_2\xi_2)}.
$$

Because the exponential function is injective on

$$
\mathbb R,
$$

this implies

$$
G(r_1\xi_1)=G(r_2\xi_2).
$$

Now divide the equality

$$
\xi_1 e^{G(r_1\xi_1)}=\xi_2 e^{G(r_2\xi_2)}
$$

by the common positive real number

$$
e^{G(r_1\xi_1)}=e^{G(r_2\xi_2)}.
$$

We obtain

$$
\xi_1=\xi_2.
$$

Denote this common unit complex number by

$$
\xi.
$$

Then

$$
z_1=r_1\xi,
\qquad
z_2=r_2\xi,
$$

and the equality of Green values becomes

$$
G(r_1\xi)=G(r_2\xi).
$$

But the function

$$
r\longmapsto G(r\xi)
$$

is strictly increasing on

$$
(4,\infty).
$$

Since

$$
r_1,r_2>4,
$$

strict monotonicity forces

$$
r_1=r_2.
$$

Therefore

$$
z_1=r_1\xi=r_2\xi=z_2.
$$

This proves that

$$
\phi|_V
$$

is injective.

## Consistency check

Injectivity on

$$
V
$$

does **not** imply that

$$
\phi(V)=\Omega.
$$

Indeed, the point

$$
\phi(4)
$$

lies in

$$
\Omega
$$

but cannot belong to

$$
\phi(V),
$$

since

$$
4\notin V.
$$

So this proof is consistent with the earlier refutation of the false
positive-constant-degree statement for the restricted map

$$
\phi|_V:V\to\Omega.
$$
