# Remaining problem: classical global Böttcher theorem at $c=2$

Let

$$
f(z)=z^2+2,
\qquad
U_\infty=\{z:\|f^{\circ n}(z)\|\to\infty\},
$$

and let $G$ be the Green function of $f$ on $U_\infty$.

Prove the theorem represented in Lean by

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

for the genuine logarithmic-series near-infinity coordinate currently formalized
as

```lean
MLC.logSeriesBottcherApprox (2 : ℂ)
```

The near-infinity part is already checked in Lean. The remaining mathematical
problem is to extend this coordinate from the canonical outside region to the
whole basin.

Concretely, construct a holomorphic map

$$
\Phi:U_\infty\to\{w:|w|>1\}
$$

such that:

1. $\Phi(f(z))=\Phi(z)^2$ for all $z\in U_\infty$;
2. $|\Phi(z)|=e^{G(z)}$ for all $z\in U_\infty$;
3. $\Phi(z)/z\to 1$ as $z\to\infty$;
4. on the canonical outside region, $\Phi$ agrees with
   `MLC.logSeriesBottcherApprox (2 : ℂ)`.

The current candidate extension is the principal pullback along an escaping
iterate:

```lean
Quadratic.basinLogSeriesExtensionCandidate (2 : ℂ)
```

The exact remaining Lean target for this candidate is:

```lean
Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)
```

The main obstacle is proving coherent branch independence for the $2^n$-roots
used in the pullback.
