# Expert handoff: final remaining theorems at `c = 2`

Let
\[
V=\{z\in\mathbf C:\ |z|>4\},\qquad \Omega=\{w\in\mathbf C:\ |w|>1\},
\]
and let
\[
\phi:V\to\Omega
\]
be the restricted outside Böttcher map for \(f(z)=z^2+2\).

The current root closes from exactly the following two inputs.

## Theorem A: generator calculation for the covering degree

Assume:

1. \(\phi\) is proper;
2. \(\phi\) is a local homeomorphism;
3. for some \(R>4\), the loop
   \[
   \Gamma_R(t)=\phi(Re^{2\pi i t})
   \]
   is freely homotopic in \(\Omega\) to the positive exterior circle
   \[
   C_R(t)=Re^{2\pi i t}.
   \]

Lean already derives from (1) and (2) that \(\phi\) is a finite-sheeted covering
of constant degree \(d\ge 1\).

**Problem.** Prove that \(d=1\). Equivalently, prove that some fiber of \(\phi\)
has cardinality \(1\), hence every fiber has cardinality \(1\).

**Standard route.** For a connected \(d\)-sheeted covering between annuli, the
induced map on \(\pi_1\cong \mathbf Z\) is multiplication by \(\pm d\). The free
homotopy assumption identifies \([\Gamma_R]\) with the positive generator of
\(\pi_1(\Omega)\), so \(\pm d=1\), hence \(d=1\).

**Exact Lean target.**

```lean
def RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo : Prop :=
  ∀ (h_cont : Continuous (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (d : ℕ), 0 < d →
      (∀ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = d) →
        (∃ R : ℝ, ∃ hR : 4 < R,
          Nonempty
            (ContinuousMap.Homotopy
              (exteriorCircleLoopTwo R hR)
              ((ContinuousMap.mk _ h_cont).comp
                (outsideOpenCircleLoopTwo R hR)))) →
          d = 1
```

Lean already derives from this the coarser Bottcher-facing corollary
`RestrictedAnnulusCoveringDegreeOneStepTwo`.

## Theorem B: direct proper/local witness for the restricted map

Prove directly for the same restricted outside Böttcher map \(\phi:V\to\Omega\)
that:

1. \(\phi\) is proper;
2. \(\phi\) is a local homeomorphism.

This is the exact remaining analytic ingress theorem if one wants to remove the
classical witness-scope half of the root kernel as well.

**Exact Lean target.**

```lean
def DirectProperLocalWitnessTwo : Prop :=
  IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))
```

## Root axiom currently used

```lean
MLC.restrictedWindingKernelTwo :
  DirectProperLocalWitnessTwoScope ∧
    Mlc.Bottcher.DegreeOne.RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo
```

So:

1. **Theorem A** is the primary remaining algebraic-topology theorem.
2. **Theorem B** is the remaining direct analytic witness theorem needed only if
   we also want to eliminate the classical witness-scope half of the root axiom.
