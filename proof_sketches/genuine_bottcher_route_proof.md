# Proof sketch: basin extension for the genuine Böttcher coordinate

The current Lean development has already constructed the canonical
near-infinity Böttcher coordinate

```lean
MLC.logSeriesBottcherApprox c
```

and proved, for every $c$, the theorem-facing package

```lean
Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox c
```

Thus the remaining issue for the current root-facing theorem surface

```lean
Quadratic.UnifiedGlobalBottcherTheoremFor (2 : ℂ)
```

is not the local coordinate at infinity. It is the extension from the canonical
outside region to the full basin of infinity together with the matching inverse
package on the exterior.

Equivalently, the theorem-facing Böttcher side is reduced to building a
`LogSeriesBasinExtensionDataFor (2 : ℂ)` plus a compatible
`GenuineBottcherInversePackageFor`; the root no longer needs any separate
sequence-level proxy axiom once those are available.

In particular, the remaining issue for

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

is still the same basin-extension problem.

## Candidate extension

For $z\in U_\infty$, choose an escape time $N$ such that

$$
f^{\circ N}(z)
$$

lies in the canonical outside region. Define

$$
\Phi(z)
  =
  \left(
    \Phi_\infty(f^{\circ N}(z))
  \right)^{1/2^N},
$$

where $\Phi_\infty$ is the near-infinity coordinate
`logSeriesBottcherApprox` and the root branch is chosen coherently along the
orbit.

In Lean this candidate is represented by

```lean
Quadratic.principalPullbackLogSeriesBottcher
Quadratic.basinLogSeriesExtensionCandidate
```

The first escape time is represented by

```lean
Quadratic.basinEscapeTime
```

## What must be proved

The core coherence theorem is:

```lean
Quadratic.PrincipalPullbackCoherentDataFor (2 : ℂ)
```

It packages the remaining requirements:

1. agreement with `logSeriesBottcherApprox` on the outside region;
2. exterior-valuedness on the basin;
3. basin characterization by exterior norm;
4. semiconjugacy $\Phi(f(z))=\Phi(z)^2$;
5. differentiability on the basin;
6. Green-function modulus identity;
7. normalization at infinity.

The first item is already checked by

```lean
Quadratic.basinLogSeriesExtensionCandidate_extends_near
```

The remaining items depend on coherent branch independence for the pullback
roots.

## Resulting theorem

Once `PrincipalPullbackCoherentDataFor (2 : ℂ)` is proved and the same basin
extension candidate is equipped with the matching exterior inverse package,
Lean already has the reductions

```lean
Quadratic.classicalGlobalBottcherTheoremFor_of_principalPullbackCoherentData
Quadratic.unifiedGlobalBottcherTheoremFor_of_principalPullbackCoherentData
```

and, for the Route-C theorem surface,

```lean
Quadratic.unifiedGlobalBottcherTheoremFor_of_classicalGlobalExtensionFromNearInfinityData
```

which yield

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
Quadratic.UnifiedGlobalBottcherTheoremFor (2 : ℂ)
```

So the next proof task is still exactly the coherent pullback / anchored
global-log theorem producing the basin extension and inverse package, not
another construction of the near-infinity coordinate.
