# \(c=2\)

\[
f(z)=z^2+2,\qquad
\mathcal B_\infty=\{z\in\mathbb C:\ f^{\circ n}(z)\to\infty\},\qquad
\Omega=\{w\in\mathbb C:\ |w|>1\},
\]
\[
V=\{z\in\mathbb C:\ |z|>4\},\qquad
G(z)=\lim_{n\to\infty}2^{-n}\log^+|f^{\circ n}(z)|.
\]

Let \(\phi:\mathcal B_\infty\to\Omega\) be the normalized basin B\"ottcher coordinate:
\[
\phi(f(z))=\phi(z)^2,\qquad
|\phi(z)|=e^{G(z)}\quad(z\in\mathcal B_\infty),\qquad
\lim_{\substack{z\to\infty\\ z\in\mathcal B_\infty}}\frac{\phi(z)}{z}=1.
\]

Prove
\[
\exists\,\Psi:\Omega\to\mathcal B_\infty
\]
such that
\[
\forall w\in\Omega,\qquad \phi(\Psi(w))=w,
\]
\[
\forall z\in V,\qquad \Psi(\phi(z))=z.
\]
