# Proof of Remaining problem 1: genuine holomorphic Böttcher coordinate at $$c=2$$

Let

$$
f(z)=z^2+2,
\qquad
U_\infty=\mathbb C\setminus K(f),
\qquad
\Omega=\{w\in\mathbb C:|w|>1\},
$$

and let $$G:U_\infty\to(0,\infty)$$ be the Green function of $$f$$.

## Claim

There exists a holomorphic map

$$
\Phi:U_\infty\to\Omega
$$

such that

$$
\Phi(f(z))=\Phi(z)^2
\qquad\text{for every }z\in U_\infty,
$$

$$
|\Phi(z)|=e^{G(z)}
\qquad\text{for every }z\in U_\infty,
$$

and

$$
\lim_{z\to\infty}\frac{\Phi(z)}{z}=1.
$$

## Proof

This is the classical global Böttcher theorem for polynomials. For a monic
polynomial $$P(z)=z^d+a_{d-1}z^{d-1}+\cdots+a_0$$ of degree $$d\geq 2$$ there
exists a unique holomorphic map

$$
\Phi_P:A_\infty(P)\to\{w\in\mathbb C:|w|>1\},
$$

defined on the full basin of infinity $$A_\infty(P)$$, such that

$$
\Phi_P(P(z))=\Phi_P(z)^d
\qquad\text{and}\qquad
\lim_{z\to\infty}\frac{\Phi_P(z)}{z}=1.
$$

See, for example, Douady--Hubbard, *Étude dynamique des polynômes complexes*,
Part I, or Milnor, *Dynamics in One Complex Variable*, §9. Applying this
theorem to $$P=f(z)=z^2+2$$ gives a holomorphic map

$$
\Phi:U_\infty\to\Omega
$$

such that

$$
\Phi(f(z))=\Phi(z)^2
\qquad\text{for all }z\in U_\infty,
$$

and

$$
\lim_{z\to\infty}\frac{\Phi(z)}{z}=1.
$$

It remains to identify its modulus. Set

$$
u(z)=\log|\Phi(z)|
\qquad (z\in U_\infty).
$$

Because $$\Phi$$ is holomorphic and never vanishes on $$U_\infty$$, the
function $$u$$ is harmonic on $$U_\infty$$. The functional equation for
$$\Phi$$ implies

$$
u(f(z))=\log|\Phi(f(z))|
=\log|\Phi(z)^2|
=2\log|\Phi(z)|
=2u(z).
$$

The normalization at infinity gives

$$
u(z)-\log|z|
=\log\left|\frac{\Phi(z)}{z}\right|
\longrightarrow 0
\qquad\text{as }z\to\infty.
$$

But the Green function of a monic polynomial is characterized as the unique
harmonic function $$G$$ on $$U_\infty$$ satisfying

$$
G(f(z))=2G(z)
\qquad\text{and}\qquad
G(z)-\log|z|\to 0
\quad\text{as }z\to\infty.
$$

Therefore $$u=G$$ on $$U_\infty$$, and hence

$$
|\Phi(z)|=e^{u(z)}=e^{G(z)}
\qquad\text{for every }z\in U_\infty.
$$

This proves the statement.

## Remark

For $$f(z)=z^2+2$$ the filled Julia set is disconnected, so the resulting
global Böttcher coordinate is a holomorphic semiconjugacy

$$
\Phi:U_\infty\to\Omega,
$$

not a biholomorphism. The claim proved above does not assert injectivity, so
there is no contradiction here.
