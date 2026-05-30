# Proof of Obstruction 1: no exact preimages along the canonical sequence approaching $$1$$

Let

$$
f(z)=z^2+2,
\qquad
w_n=1+\frac{1}{n+1},
$$

let $$G$$ be the Green function of $$f$$, and define

$$
\phi(z)=
\begin{cases}
\dfrac{z}{|z|}\,e^{G(z)}, & z\neq 0,\\[1ex]
e^{G(0)}, & z=0.
\end{cases}
$$

We prove that there is no sequence $$z_n\in\mathbb C$$ with $$\phi(z_n)=w_n$$ for every $$n\geq 0$$.

## Proof

Assume for contradiction that such a sequence $$\{z_n\}_{n\geq 0}$$ exists.

Since $$w_n\to 1$$, the sequence $$\{w_n\}$$ is bounded. In fact,

$$
1<w_n\leq 2
\qquad \text{for all } n.
$$

Because $$|\phi(z)|=e^{G(z)}$$ for every $$z\in\mathbb C$$, we obtain

$$
e^{G(z_n)}=|\phi(z_n)|=|w_n|=w_n,
$$

hence

$$
G(z_n)=\log w_n \longrightarrow 0.
$$

We claim that $$\{z_n\}$$ is bounded. For the monic polynomial $$f(z)=z^2+2$$, the Green function satisfies the standard asymptotic relation

$$
G(z)-\log |z|\longrightarrow 0
\qquad \text{as } |z|\to\infty.
$$

Therefore there exist constants $$R>0$$ and $$C>0$$ such that

$$
|z|\geq R
\qquad \Longrightarrow \qquad
\log |z|\leq G(z)+C.
$$

Since $$G(z_n)=\log w_n\leq \log 2$$, it follows that whenever $$|z_n|\geq R$$,

$$
\log |z_n|\leq \log 2 + C,
$$

so

$$
|z_n|\leq e^{\log 2 + C}.
$$

Thus $$\{z_n\}$$ is bounded. By Bolzano-Weierstrass, it has a convergent subsequence $$z_{n_k}\to a\in\mathbb C$$.

The Green function is continuous on $$\mathbb C$$, so

$$
G(a)=\lim_{k\to\infty} G(z_{n_k})=0.
$$

Hence $$a$$ belongs to the filled Julia set $$K(f)$$.

Now $$0\notin K(f)$$, because

$$
0 \mapsto 2 \mapsto 6 \mapsto 38 \mapsto \cdots
$$

and this orbit escapes to $$\infty$$. Therefore $$a\neq 0$$.

Since $$a\neq 0$$, the map $$\phi$$ is continuous at $$a$$, and so

$$
\phi(a)=\lim_{k\to\infty}\phi(z_{n_k})
=\lim_{k\to\infty} w_{n_k}
=1.
$$

But $$a\in K(f)$$ implies $$G(a)=0$$, and because $$a\neq 0$$ we have

$$
\phi(a)=\frac{a}{|a|}.
$$

Thus $$\phi(a)=1$$ forces

$$
\frac{a}{|a|}=1,
$$

so $$a$$ is a nonnegative real number.

This is impossible: every nonnegative real number escapes under iteration of $$f$$. Indeed, if $$x\geq 0$$, then

$$
f(x)=x^2+2>x.
$$

After one step the orbit lies in $$[2,\infty)$$, and for every $$y\geq 2$$ one has

$$
f(y)=y^2+2\geq y+1.
$$

Therefore the real orbit $$x,f(x),f^{\circ 2}(x),\dots$$ is eventually strictly increasing with increments at least $$1$$, so it tends to $$+\infty$$. Hence no nonnegative real point belongs to $$K(f)$$.

This contradiction proves that no sequence $$\{z_n\}_{n\geq 0}$$ with $$\phi(z_n)=w_n$$ for all $$n$$ can exist.
