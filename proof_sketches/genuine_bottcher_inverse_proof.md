# Proof of Remaining problem 2: exterior inverse package for the genuine Böttcher coordinate at $$c=2$$

Let

$$
f(z)=z^2+2,
\qquad
U_\infty=\mathbb C\setminus K(f),
\qquad
V=\{z\in\mathbb C:|z|>4\},
\qquad
\Omega=\{w\in\mathbb C:|w|>1\},
$$

and let

$$
\Phi:U_\infty\to\Omega
$$

be the holomorphic map supplied by Remaining problem 1, so that

$$
\Phi(f(z))=\Phi(z)^2,
\qquad
|\Phi(z)|=e^{G(z)},
\qquad
\frac{\Phi(z)}{z}\to 1
\quad(z\to\infty).
$$

## Claim

There exists a map

$$
\Psi:\Omega\to U_\infty
$$

such that

$$
\Phi(\Psi(w))=w
\qquad\text{for every }w\in\Omega,
$$

and

$$
\Psi(\Phi(z))=z
\qquad\text{for every }z\in V.
$$

## Proof

The proof is purely set-theoretic once two facts are recorded:

1. $$\Phi$$ is surjective onto $$\Omega$$.
2. The restriction $$\Phi|_V$$ is injective.

After these are established, define $$\Psi$$ by taking the genuine inverse of
$$\Phi|_V$$ on $$\Phi(V)$$ and choosing an arbitrary preimage for each
$$w\in\Omega\setminus \Phi(V)$$.

We now justify the two facts.

### 1. Surjectivity of $$\Phi$$

The same global Böttcher theorem used in the proof of Remaining problem 1 gives
the map

$$
\Phi:U_\infty\to\Omega
$$

as a holomorphic map onto the full exterior domain $$\Omega$$. Equivalently, it
realizes the basin dynamics on $$U_\infty$$ as a holomorphic semiconjugacy to
the squaring map on $$\Omega$$. Thus

$$
\Phi(U_\infty)=\Omega.
$$

### 2. Injectivity of $$\Phi$$ on $$V=\{|z|>4\}$$

Near infinity the Böttcher coordinate is the classical normalized local
coordinate, and it is conformal on an exterior neighborhood of infinity. For
the specific polynomial $$f(z)=z^2+2$$ the standard local construction already
works on $$V=\{|z|>4\}$$, because on this region

$$
\left|\frac{f(z)-z^2}{z^2}\right|
=\frac{2}{|z|^2}
<\frac18.
$$

Hence the usual root-limit or infinite-product construction of the local
Böttcher coordinate converges normally on $$V$$ and yields a holomorphic
injective map

$$
\Phi_V:V\to\Omega
$$

with

$$
\Phi_V(f(z))=\Phi_V(z)^2
\qquad\text{and}\qquad
\frac{\Phi_V(z)}{z}\to 1
\quad(z\to\infty).
$$

By uniqueness of the normalized Böttcher coordinate near infinity, the global
map from Remaining problem 1 and the local coordinate on $$V$$ agree on $$V$$:

$$
\Phi|_V=\Phi_V.
$$

Therefore $$\Phi|_V$$ is injective.

### 3. Construction of $$\Psi$$

Since $$\Phi|_V$$ is injective, it has a genuine inverse

$$
(\Phi|_V)^{-1}:\Phi(V)\to V.
$$

Since $$\Phi$$ is surjective, for every

$$
w\in\Omega\setminus\Phi(V)
$$

we may choose one point

$$
z_w\in U_\infty
\qquad\text{with}\qquad
\Phi(z_w)=w.
$$

Define

$$
\Psi(w)=
\begin{cases}
(\Phi|_V)^{-1}(w), & w\in\Phi(V),\\[1ex]
z_w, & w\in\Omega\setminus\Phi(V).
\end{cases}
$$

Then for every $$w\in\Omega$$ we have

$$
\Phi(\Psi(w))=w.
$$

Indeed, this is obvious on $$\Phi(V)$$ by definition of the inverse branch, and
it holds on $$\Omega\setminus\Phi(V)$$ by the choice of $$z_w$$.

Finally, if $$z\in V$$, then $$\Phi(z)\in\Phi(V)$$, so

$$
\Psi(\Phi(z))
=(\Phi|_V)^{-1}(\Phi(z))
=z.
$$

Thus $$\Psi$$ satisfies both required identities.

This proves the claim.

## Remark

No regularity of $$\Psi$$ is requested in the statement. The argument above
therefore only needs surjectivity of the global Böttcher coordinate and
injectivity of its restriction to $$V$$.
