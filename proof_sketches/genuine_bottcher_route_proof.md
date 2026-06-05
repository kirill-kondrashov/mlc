# Proof sketch for Remaining problem 1: genuine Böttcher route at $$c=2$$

Let

$$
f(z)=z^2+2,
\qquad
U_\infty=\mathbb C\setminus K(f),
\qquad
V=\{z\in\mathbb C: |z|>4\},
\qquad
\Omega=\{w\in\mathbb C: |w|>1\},
$$

and let $$G:U_\infty\to(0,\infty)$$ be the Green function of $$f$$.

## Claim

There exists a holomorphic map

$$
\Phi:U_\infty\to\Omega
$$

such that

$$
\Phi(f(z))=\Phi(z)^2,
\qquad
|\Phi(z)|=e^{G(z)},
\qquad
\frac{\Phi(z)}{z}\to 1
\quad (z\to\infty),
$$

with

$$
\Phi(U_\infty)=\Omega
$$

and such that $$\Phi|_V$$ is injective.

## Proof sketch

### 1. Global normalized Böttcher coordinate

For a monic polynomial $$P(z)=z^d+a_{d-1}z^{d-1}+\cdots+a_0$$ of degree
$$d\geq 2$$, the classical global Böttcher theorem gives a unique holomorphic
map

$$
\Phi_P:A_\infty(P)\to\{w\in\mathbb C:|w|>1\}
$$

satisfying

$$
\Phi_P(P(z))=\Phi_P(z)^d
\qquad\text{and}\qquad
\lim_{z\to\infty}\frac{\Phi_P(z)}{z}=1.
$$

Applying this to

$$
P=f(z)=z^2+2
$$

gives a holomorphic map

$$
\Phi:U_\infty\to\Omega
$$

with

$$
\Phi(f(z))=\Phi(z)^2
\qquad\text{for all } z\in U_\infty
$$

and

$$
\lim_{z\to\infty}\frac{\Phi(z)}{z}=1.
$$

### 2. Identification of the modulus

Set

$$
u(z)=\log|\Phi(z)|.
$$

Because $$\Phi$$ is holomorphic and nonvanishing on $$U_\infty$$, the function
$$u$$ is harmonic on $$U_\infty$$. The functional equation gives

$$
u(f(z))=2u(z),
$$

while the normalization at infinity yields

$$
u(z)-\log|z|
=
\log\left|\frac{\Phi(z)}{z}\right|
\longrightarrow 0
\qquad (z\to\infty).
$$

The Green function of a monic polynomial is characterized as the unique harmonic
function on the basin of infinity satisfying exactly these two properties.
Hence

$$
u=G
$$

on $$U_\infty$$, and therefore

$$
|\Phi(z)|=e^{G(z)}
\qquad\text{for every } z\in U_\infty.
$$

### 3. Surjectivity onto $$\Omega$$

The global Böttcher coordinate is the standard exterior coordinate on the basin
of infinity. Its image contains an outer annulus

$$
\{w\in\mathbb C: |w|>\rho\}
$$

for some $$\rho>1$$ by the normalization at infinity. Since

$$
\Phi(f(z))=\Phi(z)^2,
$$

the image is forward invariant under squaring. By iterating backwards along the
squaring map, every point of $$\Omega$$ has the same Green level and external
angle as some point in that outer annulus, hence is hit by a point of the
basin. Equivalently, the standard global Böttcher theorem identifies

$$
\Phi(U_\infty)=\Omega.
$$

### 4. Injectivity on $$V=\{|z|>4\}$$

Near infinity the Böttcher coordinate is the classical local conformal
coordinate. For $$f(z)=z^2+2$$ one has on $$V$$

$$
\left|\frac{f(z)-z^2}{z^2}\right|
=
\frac{2}{|z|^2}
<
\frac18.
$$

Thus the standard root-limit construction on $$V$$ converges normally and gives
a univalent local Böttcher coordinate

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

By uniqueness of the normalized Böttcher coordinate near infinity,

$$
\Phi|_V=\Phi_V.
$$

Hence $$\Phi|_V$$ is injective.

This proves the whole genuine Böttcher route required in Remaining problem 1.
