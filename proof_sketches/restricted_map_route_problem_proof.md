# The current restricted-map route problem is false as stated

Let
$$
V=\{z\in\mathbb C:\lvert z\rvert>4\},\qquad \Omega=\{w\in\mathbb C:\lvert w\rvert>1\},
$$
and let
$$
\phi:V\to\Omega
$$
be the restricted outside Böttcher map at $$c=2$$.

The current draft asks to prove:

1. $$\phi$$ is proper;
2. $$\phi$$ is a local homeomorphism.

The second statement is true, but the first one is false. Hence the draft problem has no proof as written.

## Local homeomorphism

Let $$U_\infty$$ be the basin of infinity of $$f_2(z)=z^2+2$$. The classical Böttcher theorem gives a biholomorphism
$$
\Phi:U_\infty\to\Omega
$$
satisfying $$\Phi(f_2(z))=\Phi(z)^2$$ and $$\Phi(z)/z\to 1$$ as $$z\to\infty$$. Since $$V\subset U_\infty$$, the restricted map
$$
\phi=\Phi|_V:V\to\Omega
$$
is the restriction of a homeomorphism to an open subset of its domain. Therefore $$\phi$$ is a local homeomorphism.

## Counterexample to properness

Set
$$
z_*=4,\qquad z_n=4+\frac1n\quad (n\ge 1).
$$
Then $$z_*\in U_\infty$$, every $$z_n\in V$$, and $$z_n\to z_*$$ in $$\mathbb C$$.

Define
$$
w_*=\Phi(z_*),\qquad w_n=\Phi(z_n)\quad (n\ge 1).
$$
By continuity of $$\Phi$$ on $$U_\infty$$, we have $$w_n\to w_*$$. Since $$w_*\in\Omega$$, the set
$$
K=\{w_*\}\cup\{w_n:n\ge 1\}
$$
is compact in $$\Omega$$.

We now compute the preimage of $$K$$ under $$\phi$$. Because $$\Phi$$ is injective on $$U_\infty$$, we have:

1. $$\phi(z_n)=w_n$$ for every $$n\ge 1$$;
2. $$w_*$$ has no preimage in $$V$$, because its unique preimage under $$\Phi$$ is $$z_*=4\notin V$$.

Hence
$$
\phi^{-1}(K)=\{z_n:n\ge 1\}.
$$

This set is not compact in $$V$$. Indeed, the sequence $$z_n$$ lies in $$\phi^{-1}(K)$$, but every subsequence of $$z_n$$ converges in $$\mathbb C$$ to the same limit $$z_*=4\notin V$$. Therefore $$\{z_n:n\ge 1\}$$ has no convergent subsequence with limit in $$V$$. Since $$V$$ is a metric space, compactness is equivalent to sequential compactness, so $$\phi^{-1}(K)$$ is not compact in $$V$$.

Thus $$\phi$$ is not a proper map $$V\to\Omega$$.

## Conclusion

The original properness formulation of Problem B is false: the restricted outside Böttcher map is a local homeomorphism, but it is not proper as a map from $$V$$ to the full exterior domain $$\Omega$$. Consequently there is no rigorous proof of that old statement.

The remaining truthful witness-side statement is therefore weaker: prove local homeomorphy of $$\phi$$ and prove that the restricted fibers
$$
F_w=\{z\in V:\phi(z)=w\}
$$
have one positive constant finite cardinality independent of $$w\in\Omega$$.
