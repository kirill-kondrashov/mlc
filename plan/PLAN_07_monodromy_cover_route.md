# PLAN 07: Monodromy-cover route for basin Böttcher extension

**Status:** PLANNED  
**Depends on:** `PLAN_06_global_bottcher_package.md`

## Goal

Construct the basin extension data needed for

```lean
Quadratic.ClassicalGlobalBottcherTheoremFor (2 : ℂ)
```

by proving the cover-based seam

```lean
Quadratic.MonodromyTrivializingCoverBasinExtensionDataFor (2 : ℂ)
```

and then using the checked reduction

```lean
classicalGlobalBottcherTheoremFor_of_monodromyTrivializingCoverData
```

## Current formalized starting point

The near-infinity coordinate is already proved:

```lean
MLC.logSeriesBottcherApprox c
genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox
```

The finite root-choice algebra is also proved:

```lean
rootsOfUnitySet
pullbackRootSet
rootsOfUnity_smul_pullbackRootSet
pullbackRootSet_torsor_transitive
pullbackRootSet_subset_next_of_sq
logSeries_pullbackRootSet_subset_next
```

So the remaining issue is not algebraic root existence. It is analytic topology:
monodromy, covers, lifted holomorphic branches, and descent.

## Required components

### 1. Fundamental group / covering interface

Needed theorem surface:

```lean
CoveringAssociatedToKernel
```

Informal content:

Given a monodromy representation

$$
\rho : \pi_1(U_\infty) \to \varprojlim_N \mu_{2^N},
$$

construct the covering space corresponding to

$$
\ker(\rho).
$$

Current status: **missing**. The repository does not currently expose a usable
covering-space construction associated to a subgroup of the fundamental group of
the basin.

### 2. Monodromy representation

Needed theorem surface:

```lean
PullbackRootMonodromyRepresentation
```

Informal content:

For each level `N`, analytic continuation of a local root branch around a basin
loop gives an element of

$$
\mu_{2^N}.
$$

The level maps must be compatible with

$$
\mu_{2^{N+1}}\to\mu_{2^N},\qquad \zeta\mapsto\zeta^2.
$$

Current status: **partially formalized algebraically**. The finite torsor
algebra is in Lean, but the analytic loop-to-monodromy map is not.

### 3. Lifted coordinate on the monodromy-trivializing cover

Needed theorem surface:

```lean
LiftedLogSeriesBottcherOnCover
```

Informal content:

On the cover associated to `ker ρ`, define a holomorphic lifted coordinate

$$
\widetilde\Phi
$$

whose pullback roots are single-valued.

Current status: **missing**. This requires the covering construction and
analytic continuation of the local branch.

### 4. Deck invariance / descent

Needed theorem surface:

```lean
LiftedBottcherDeckInvariant
```

Informal content:

Show that the lifted coordinate is constant on fibers of the cover projection:

$$
\widetilde\Phi(x)=\widetilde\Phi(y)
\quad\text{whenever}\quad
p(x)=p(y).
$$

Then define a single-valued basin coordinate

$$
\Phi(z)=\widetilde\Phi(x), \qquad p(x)=z.
$$

Current status: **missing and decisive**. If deck invariance fails, the cover
only produces a multivalued coordinate, not the required Böttcher coordinate on
the original basin.

### 5. Package into the existing seam

Once the cover data is available, fill:

```lean
MonodromyTrivializingCoverBasinExtensionDataFor (2 : ℂ)
```

Then use:

```lean
classicalGlobalBottcherTheoremFor_of_monodromyTrivializingCoverData
```

## Exact obstruction

The obstruction is nontrivial monodromy. A basin loop may act on a chosen
`2^N`-root by

$$
w \mapsto \rho_N(\gamma)\,w,
\qquad
\rho_N(\gamma)\in\mu_{2^N}.
$$

The desired single-valued coordinate requires

$$
\rho_N(\gamma)=1
$$

for all relevant loops and all compatible levels.

## Recommended next formal step

The first theorem surface for the monodromy representation is now formalized:

```lean
PullbackRootMonodromyRepresentation
PullbackRootMonodromyRepresentation.Trivial
PullbackRootMonodromyRepresentation.smul_pullbackRootSet
PullbackRootMonodromyRepresentation.trivial_smul_eq
EscapeTimeIndependentPullbackDataFor
MonodromyTrivialPullbackDataFor
```

This records:

1. level-wise maps to `rootsOfUnitySet (2^N)`;
2. compatibility under squaring;
3. action on `pullbackRootSet`;
4. the algebraic fact that trivial monodromy fixes every finite-level pullback
   root;
5. the analytic consequence still needed: escape-time-independent pullback
   values.

The remaining formal step is to construct `MonodromyTrivialPullbackDataFor
(2 : ℂ)` from actual basin loop/monodromy topology. This still requires either:

1. a covering-space construction and deck-invariance/descent proof; or
2. a direct analytic continuation theorem proving trivial monodromy for the
   normalized branch.

The focused formalization plan for this analytic-continuation/monodromy layer is
`plan/PLAN_08_analytic_continuation_monodromy.md`.
