# Expert handoff: exact remaining theorems at `c = 2`

Let
\[
V=\{z\in\mathbf C:\ |z|>4\},\qquad \Omega=\{w\in\mathbf C:\ |w|>1\},
\]
and let
\[
\phi:V\to\Omega
\]
be the restricted outside Böttcher map for \(f(z)=z^2+2\).

The checked root currently uses exactly

```lean
MLC.restrictedWindingKernelTwo :
  DirectProperLocalWitnessTwoScope ∧
    Mlc.Bottcher.DegreeOne.RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo
```

where

```lean
def DirectProperLocalWitnessTwoScope : Prop := ¬¬ DirectProperLocalWitnessTwo
```

So there are exactly two remaining human-level targets.

## Theorem A: generator calculation for the covering degree

Assume:

1. \(\phi\) is proper;
2. \(\phi\) is a local homeomorphism;
3. there exists an integer \(d\ge 1\) such that every fiber \(\phi^{-1}(w)\), \(w\in\Omega\), has cardinality exactly \(d\);
4. for some \(R>4\), the loop
   \[
   t\mapsto \phi(Re^{2\pi i t})
   \]
   is freely homotopic in \(\Omega\) to the positive exterior circle
   \[
   t\mapsto Re^{2\pi i t}.
   \]

**Claim.** Prove that \(d=1\).

This is the exact remaining algebraic-topology step. Lean already supplies the
constant positive covering degree from properness + local homeomorphy, and it
already supplies the large-circle homotopy; the missing proof is only the
fundamental-group / covering-degree calculation.

**Exact Lean target.**

```lean
def RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo : Prop :=
  ∀ (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (d : ℕ), 0 < d →
      (∀ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = d) →
        (∃ R : ℝ, ∃ hR : 4 < R,
          Nonempty
            (ContinuousMap.Homotopy
              (exteriorCircleLoopTwo R hR)
              ((ContinuousMap.mk _ h_local.continuous).comp
                (outsideOpenCircleLoopTwo R hR)))) →
          d = 1
```

Lean already derives the constant positive degree from (1) and (2), so the
remaining proof is the fundamental-group calculation under these covering
hypotheses.

Equivalent expert-language version: for a connected finite covering of annuli,
if the image of a large outer circle is freely homotopic to the positive
generator of the target annulus, then the covering degree is \(1\).

## Theorem B: constructive proper/local witness for the restricted map

Prove directly that the same restricted outside Böttcher map \(\phi:V\to\Omega\)
is:

1. proper;
2. a local homeomorphism.

This is the remaining analytic ingress theorem. A constructive proof of this
theorem removes the current classical scope gate `DirectProperLocalWitnessTwoScope`.

**Exact Lean target.**

```lean
def DirectProperLocalWitnessTwo : Prop :=
  IsProperMap (bottcher_map_outside_open_to_exterior (2 : ℂ)) ∧
    IsLocalHomeomorph (bottcher_map_outside_open_to_exterior (2 : ℂ))
```

## Priority

1. **Primary remaining theorem:** `RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo`.
2. **Secondary remaining theorem:** `DirectProperLocalWitnessTwo`, only needed to remove the remaining classical scope gate.
