# Proof of Problem 1: basin-valued exterior inverse at $$c=2$$

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

The proof uses two previously established facts.

## Auxiliary input

### 1. Exterior surjectivity

For every

$$
w\in\Omega
$$

there exists at least one

$$
z\in U_\infty
$$

such that

$$
\phi(z)=w.
$$

### 2. Injectivity on the outside-open region

The restriction

$$
\phi|_V:V\to\Omega
$$

is injective. This is proved in
`proof_sketches/outside_open_injectivity_problem_proof.md`.

## Proof

For each

$$
w\in\Omega
$$

define the fiber

$$
F_w=\{z\in U_\infty : \phi(z)=w\}.
$$

By exterior surjectivity,

$$
F_w\neq\varnothing
$$

for every

$$
w\in\Omega.
$$

Now consider the subset

$$
F_w\cap V.
$$

If this set is nonempty, then it contains exactly one point: indeed, if

$$
z_1,z_2\in F_w\cap V,
$$

then

$$
\phi(z_1)=w=\phi(z_2),
$$

and injectivity of

$$
\phi|_V
$$

gives

$$
z_1=z_2.
$$

We now define

$$
\Psi:\Omega\to U_\infty
$$

by the following rule:

1. if
   $$
   F_w\cap V\neq\varnothing,
   $$
   let
   $$
   \Psi(w)
   $$
   be the unique point of
   $$
   F_w\cap V;
   $$
2. if
   $$
   F_w\cap V=\varnothing,
   $$
   choose any point
   $$
   \Psi(w)\in F_w.
   $$

This definition is legitimate because each fiber

$$
F_w
$$

is nonempty.

By construction,

$$
\Psi(w)\in F_w
$$

for every

$$
w\in\Omega,
$$

so

$$
\phi(\Psi(w))=w
$$

for every

$$
w\in\Omega.
$$

This proves the required right-inverse identity.

It remains to prove the left-inverse identity on

$$
V.
$$

Fix

$$
z\in V
$$

and set

$$
w=\phi(z).
$$

Then

$$
z\in F_w\cap V,
$$

so

$$
F_w\cap V\neq\varnothing.
$$

By injectivity of

$$
\phi|_V,
$$

the set

$$
F_w\cap V
$$

has exactly one element, namely

$$
z.
$$

By the definition of

$$
\Psi,
$$

when

$$
F_w\cap V\neq\varnothing
$$

the value

$$
\Psi(w)
$$

is chosen to be that unique point. Therefore

$$
\Psi(\phi(z))=\Psi(w)=z.
$$

This proves

$$
\Psi(\phi(z))=z
$$

for every

$$
z\in V.
$$

Hence the required map

$$
\Psi:\Omega\to U_\infty
$$

exists.

## Consistency check

This statement does **not** say that every

$$
w\in\Omega
$$

has a preimage in

$$
V.
$$

That stronger claim is false. For example, if

$$
w=\phi(4),
$$

then

$$
w\in\Omega
$$

but

$$
w\notin \phi(V),
$$

because

$$
4\notin V.
$$

The point of the present theorem is exactly that

$$
\Psi(w)
$$

is only required to lie in

$$
U_\infty,
$$

and it is required to land in

$$
V
$$

only for those

$$
w
$$

which already belong to

$$
\phi(V).
$$
