# Proof sketch for Remaining problem 2: local parameter extension near $$c=2$$

For each parameter $$c\in\mathbb C$$, let

$$
f_c(z)=z^2+c,
\qquad
U_\infty(c)=\mathbb C\setminus K(f_c),
\qquad
G_c:U_\infty(c)\to(0,\infty).
$$

Assume the genuine normalized Böttcher route of Remaining problem 1 at
$$c=2$$.

## Claim

There exist $$r>0$$ and $$R>0$$ and a map

$$
\Phi:\{(c,z)\in\mathbb C^2 : |c-2|<r,\ |z|>R\}\to\mathbb C
$$

such that:

1. for each fixed $$c$$ with $$|c-2|<r$$, the map $$z\mapsto\Phi(c,z)$$ is
   holomorphic on $$\{|z|>R\};$$
2. for each fixed $$z$$ with $$|z|>R$$, the map $$c\mapsto\Phi(c,z)$$ is
   holomorphic on $$\{|c-2|<r\};$$
3. one has
   $$
   \Phi(c,f_c(z))=\Phi(c,z)^2;
   $$
4. one has
   $$
   \frac{\Phi(c,z)}{z}\to 1
   \qquad (z\to\infty)
   $$
   locally uniformly in $$c;$$
5. for every such $$c$$, the map extends uniquely to the normalized global
   Böttcher coordinate
   $$
   \Phi_c:U_\infty(c)\to\{w\in\mathbb C: |w|>1\};
   $$
6. for every depth $$n\geq 0$$,
   $$
   \partial\{z : G_c(z)<2^{-n}\}
   =
   \{z : G_c(z)=2^{-n}\}
   =
   \{z : |\Phi_c(z)|=e^{2^{-n}}\}.
   $$

## Proof sketch

### 1. Uniform exterior region

Choose $$r>0$$ small and then choose $$R>0$$ large so that for every parameter
with

$$
|c-2|<r
$$

one has

$$
|z|>R
\qquad\Longrightarrow\qquad
|f_c(z)|>|z|>R.
$$

This gives a uniform forward-invariant exterior region

$$
\{(c,z): |c-2|<r,\ |z|>R\}.
$$

### 2. Parameter-dependent root-limit construction near infinity

On this uniform exterior region one may choose a common holomorphic branch of
the logarithm, or equivalently compatible square-root branches, because the
iterates stay in a fixed simply connected exterior/slit domain. Define

$$
\Phi_n(c,z)=\bigl(f_c^{\circ n}(z)\bigr)^{1/2^n}
$$

using these compatible branches.

Exactly as in the classical proof of the local Böttcher theorem, the sequence
$$\Phi_n$$ is locally uniformly Cauchy on

$$
\{(c,z): |c-2|<r,\ |z|>R\}.
$$

Hence it converges locally uniformly to a limit

$$
\Phi(c,z).
$$

The convergence is locally uniform jointly in $$c$$ and $$z$$, so standard
holomorphic-parameter arguments imply:

1. for each fixed $$c$$, the map $$z\mapsto\Phi(c,z)$$ is holomorphic on
   $$\{|z|>R\};$$
2. for each fixed $$z$$, the map $$c\mapsto\Phi(c,z)$$ is holomorphic on
   $$\{|c-2|<r\}.$$

### 3. Functional equation and normalization

Passing to the limit in the defining recursion gives

$$
\Phi(c,f_c(z))=\Phi(c,z)^2
$$

on the exterior region. The same construction gives the asymptotic expansion

$$
\Phi(c,z)=z\,(1+o(1))
\qquad (z\to\infty),
$$

locally uniformly in $$c$$, hence

$$
\frac{\Phi(c,z)}{z}\to 1.
$$

### 4. Extension from the exterior region to the full basin

Fix a parameter $$c$$ with $$|c-2|<r$$. Every point of $$U_\infty(c)$$
eventually enters the region $$\{|z|>R\}$$ under iteration by $$f_c$$. For such
a point $$z$$, choose an integer $$m\geq 0$$ with

$$
f_c^{\circ m}(z)\in\{|w|>R\}.
$$

Then define

$$
\Phi_c(z)=\Phi\bigl(c,f_c^{\circ m}(z)\bigr)^{1/2^m},
$$

using the branch determined by the near-infinity construction. The functional
equation makes this independent of the chosen $$m$$, so one obtains a well
defined holomorphic map

$$
\Phi_c:U_\infty(c)\to\{w\in\mathbb C: |w|>1\}
$$

which extends the near-infinity coordinate and satisfies

$$
\Phi_c(f_c(z))=\Phi_c(z)^2,
\qquad
\frac{\Phi_c(z)}{z}\to 1.
$$

By uniqueness of the normalized Böttcher coordinate, this is exactly the global
coordinate for the parameter $$c$$.

### 5. Green-function modulus and puzzle-boundary compatibility

For each fixed $$c$$, the same argument as in Remaining problem 1 shows that the
function

$$
u_c(z)=\log|\Phi_c(z)|
$$

is harmonic on $$U_\infty(c)$$, satisfies

$$
u_c(f_c(z))=2u_c(z),
$$

and obeys

$$
u_c(z)-\log|z|\to 0
\qquad (z\to\infty).
$$

Therefore

$$
u_c=G_c,
$$

so

$$
|\Phi_c(z)|=e^{G_c(z)}.
$$

Consequently, for every depth $$n\geq 0$$,

$$
G_c(z)=2^{-n}
\qquad\Longleftrightarrow\qquad
|\Phi_c(z)|=e^{2^{-n}}.
$$

Hence

$$
\partial\{z : G_c(z)<2^{-n}\}
=
\{z : G_c(z)=2^{-n}\}
=
\{z : |\Phi_c(z)|=e^{2^{-n}}\},
$$

which is the exact equipotential compatibility needed for the parameter-puzzle
boundary interpretation.

This is the local parameter-extension package required by Remaining problem 2.
