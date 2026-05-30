# Proof of Obstruction 2: the global fixed-anchor inequality is false

Let

$$
f(z)=z^2+2,
$$

let $$G$$ be the Green function of $$f$$, and for each nonzero $$w\in\mathbb C$$ define

$$
a(w)=4\,\frac{w}{|w|}.
$$

We prove that the statement

$$
G(a(w))<\log |w|
\qquad \text{for every } w\in\mathbb C \text{ with } |w|>1
$$

is false.

## Proof

Fix any complex number $$u$$ with

$$
|u|=1.
$$

Set

$$
A=G(4u).
$$

First we show that $$A>0$$. The point $$4u$$ escapes under iteration of $$f$$, because

$$
|f(4u)|=|16u^2+2|\geq 16-2=14,
$$

and once an orbit has modulus larger than $$4$$, it tends to $$\infty$$ under the map $$z\mapsto z^2+2$$. Therefore $$4u$$ lies in the basin of infinity, and the Green function is strictly positive there:

$$
A=G(4u)>0.
$$

Now choose

$$
w=e^{A/2}u.
$$

Then

$$
|w|=e^{A/2}>1
$$

and

$$
a(w)=4\,\frac{w}{|w|}=4u.
$$

If the global fixed-anchor inequality were true, applying it to this particular $$w$$ would give

$$
A=G(4u)=G(a(w))<\log |w|=\log(e^{A/2})=\frac{A}{2}.
$$

But $$A>0$$, so the inequality $$A<\frac{A}{2}$$ is impossible.

This contradiction proves that the global statement

$$
G(a(w))<\log |w|
\qquad \text{for all } |w|>1
$$

is false.
