# Remaining basin-valued external-ray problem at c = 2

Let

$$
U_\infty=\{z\in\mathbb C:\text{$f^{\circ n}(z)\to\infty$ as }n\to\infty\},
\qquad
\Omega=\{w\in\mathbb C:\lvert w\rvert>1\},
$$

and let

$$
\phi:U_\infty\to\Omega
$$

be the Böttcher coordinate used in this repository for the quadratic polynomial

$$
f(z)=z^2+2.
$$

Also let

$$
V=\{z\in\mathbb C:\lvert z\rvert>4\}\subset U_\infty.
$$

Prove the following statement.

## Problem. Basin-valued exterior inverse for the fixed Böttcher coordinate

Prove that there exists a map

$$
\Psi:\Omega\to U_\infty
$$

such that:

1. For every $$w\in\Omega$$ one has
   $$
   \phi(\Psi(w))=w.
   $$
2. For every $$z\in V$$ one has
   $$
   \Psi(\phi(z))=z.
   $$

Equivalently, prove that $$\phi$$ admits a right inverse on all of $$\Omega$$
whose restriction to $$\phi(V)$$ is a left inverse for the restricted outside
map $$\phi|_V:V\to\Omega$$. This is the codomain-correct replacement for the
false statement that $$\phi|_V$$ should itself be surjective onto all of
$$\Omega$$.
