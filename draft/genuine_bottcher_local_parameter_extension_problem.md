# Remaining problem 2: local parameter extension near $$c=2$$

For each parameter $$c\in\mathbb C$$, let

$$
f_c(z)=z^2+c,
$$

and let

$$
U_\infty(c)=\mathbb C\setminus K(f_c),
\qquad
G_c:U_\infty(c)\to(0,\infty)
$$

be the basin of infinity and Green function of $$f_c$$.

Assume that the normalized genuine Böttcher route of Remaining problem 1 is
known at $$c=2$$.

Prove that there exist numbers $$r>0$$ and $$R>0$$ and a map

$$
\Phi:\{(c,z)\in\mathbb C^2 : |c-2|<r,\ |z|>R\}\to\mathbb C
$$

such that:

$$
\text{for each fixed } c \text{ with } |c-2|<r,\quad
z\mapsto \Phi(c,z)
$$

is holomorphic on $$\{z\in\mathbb C : |z|>R\},$$

$$
\text{for each fixed } z \text{ with } |z|>R,\quad
c\mapsto \Phi(c,z)
$$

is holomorphic on $$\{c\in\mathbb C : |c-2|<r\},$$

$$
\Phi(c,f_c(z))=\Phi(c,z)^2
\qquad
\text{whenever } |c-2|<r \text{ and } |z|>R,
$$

$$
\lim_{z\to\infty}\frac{\Phi(c,z)}{z}=1
$$

locally uniformly in $$c\in\{ |c-2|<r\},$$

and for every $$c$$ with $$|c-2|<r$$ the map $$z\mapsto\Phi(c,z)$$ extends
uniquely from $$\{|z|>R\}$$ to the normalized global Böttcher coordinate

$$
\Phi_c:U_\infty(c)\to\{w\in\mathbb C : |w|>1\}.
$$

Moreover, prove that for every depth $$n\geq 0$$ and every such parameter $$c$$,

$$
\partial\{z\in\mathbb C : G_c(z)<2^{-n}\}
=
\{z\in U_\infty(c) : G_c(z)=2^{-n}\}
=
\{z\in U_\infty(c) : |\Phi_c(z)|=e^{2^{-n}}\}.
$$
