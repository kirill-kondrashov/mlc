# \(c=2\) basin-valued exterior B\"ottcher package

\[
f(z)=z^2+2,
\qquad
\mathcal B_\infty=\{z\in\mathbb C:\ f^{\circ n}(z)\to\infty\},
\qquad
\Omega=\{w\in\mathbb C:\ |w|>1\},
\qquad
V=\{z\in\mathbb C:\ |z|>4\}.
\]

\[
G(z):=\lim_{n\to\infty}2^{-n}\log^+|f^{\circ n}(z)|.
\]

\[
\textbf{Problem.}
\]

Construct maps
\[
\phi:\mathcal B_\infty\to\Omega,
\qquad
\Psi:\Omega\to\mathcal B_\infty
\]
such that

\[
\phi(f(z))=\phi(z)^2
\qquad
(\forall z\in\mathcal B_\infty),
\]

\[
|\phi(z)|=e^{G(z)}
\qquad
(\forall z\in\mathcal B_\infty),
\]

\[
\frac{\phi(z)}{z}\to 1
\qquad
(z\to\infty,\ z\in\mathcal B_\infty),
\]

\[
\phi(\Psi(w))=w
\qquad
(\forall w\in\Omega),
\]

\[
\Psi(\phi(z))=z
\qquad
(\forall z\in V).
\]

Equivalently, prove the existence of a basin-valued normalized B\"ottcher
coordinate \(\phi\) and an exterior inverse \(\Psi\) with the above five
properties.
