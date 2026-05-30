# The current restricted fiber-degree problem is false as stated

Let
$$
V=\{z\in\mathbb C:\lvert z\rvert>4\},\qquad \Omega=\{w\in\mathbb C:\lvert w\rvert>1\},
$$
and let
$$
\phi:V\to\Omega
$$
be the restricted outside Böttcher map for $$f(z)=z^2+2$$.

The current draft asks to prove:

1. $$\phi$$ is a local homeomorphism.
2. There exists an integer $$d\ge 1$$ such that for every $$w\in\Omega$$ the fiber
   $$
   F_w=\{z\in V:\phi(z)=w\}
   $$
   has exactly $$d$$ points.

The first statement is true, but the second one is false. Hence the draft problem has no proof as written.

## Proof that $$\phi$$ is a local homeomorphism

Let $$U_\infty$$ be the basin of infinity of $$f(z)=z^2+2$$. The Böttcher theorem gives a biholomorphism
$$
\Phi:U_\infty\to\Omega
$$
satisfying $$\Phi(f(z))=\Phi(z)^2$$ and $$\Phi(z)/z\to 1$$ as $$z\to\infty$$. Since $$V\subset U_\infty$$, the restricted map
$$
\phi=\Phi|_V:V\to\Omega
$$
is the restriction of a homeomorphism to an open subset of its domain. Therefore $$\phi$$ is a local homeomorphism.

## Counterexample to the constant positive fiber-degree statement

Because $$4\in U_\infty$$, the point
$$
w_0=\Phi(4)
$$
is well defined and belongs to $$\Omega$$. We claim that
$$
F_{w_0}=\varnothing.
$$
Indeed, if $$z\in V$$ satisfied $$\phi(z)=w_0$$, then
$$
\Phi(z)=w_0=\Phi(4).
$$
Since $$\Phi$$ is injective on $$U_\infty$$, we would get $$z=4$$, contradicting $$z\in V=\{z:\lvert z\rvert>4\}$$. Thus $$F_{w_0}$$ is empty.

Now take
$$
w_1=\Phi(5).
$$
Since $$5\in V$$, we have $$5\in F_{w_1}$$. If $$z\in F_{w_1}$$, then
$$
\Phi(z)=w_1=\Phi(5),
$$
so injectivity of $$\Phi$$ on $$U_\infty$$ gives $$z=5$$. Hence
$$
F_{w_1}=\{5\}.
$$

Therefore
$$
\#F_{w_0}=0,\qquad \#F_{w_1}=1.
$$
So there cannot exist any integer $$d\ge 1$$ such that every fiber $$F_w$$ has cardinality exactly $$d$$.

## Conclusion

The current `draft/restricted_map_route_problem.md` is false. The restricted outside Böttcher map is indeed a local homeomorphism, but its fibers over the full exterior domain $$\Omega$$ do not have a positive constant cardinality: some are empty and some are singletons. Consequently there is no rigorous proof of the draft problem in its present form.
