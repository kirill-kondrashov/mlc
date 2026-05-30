# Approach-to-one preimage obstruction for the current constructive coordinate

Let

$$
f(z)=z^2+2,
$$

let $$G:\mathbb C\to\mathbb R$$ be the Green function of $$f$$, and define the current constructive coordinate

$$
\phi:\mathbb C\to\mathbb C
$$

by

$$
\phi(z)=
\begin{cases}
\dfrac{z}{|z|}\,e^{G(z)}, & z\neq 0,\\[1ex]
e^{G(0)}, & z=0.
\end{cases}
$$

For each integer $$n\geq 0$$, let

$$
w_n=1+\frac{1}{n+1}.
$$

## Obstruction 1. No exact preimages along the canonical sequence approaching $$1$$

Show that there does not exist any sequence $$z_0,z_1,z_2,\dots\in\mathbb C$$ such that

$$
\phi(z_n)=w_n
\qquad \text{for every } n\geq 0.
$$
