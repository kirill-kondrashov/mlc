# Expert handoff: remaining algebraic-topology step at `c = 2`

Let
\[
V=\{z\in\mathbf C:\ |z|>4\},\qquad \Omega=\{w\in\mathbf C:\ |w|>1\}.
\]
Let \(\phi:V\to\Omega\) be the restricted outside Böttcher map for \(f(z)=z^2+2\).

## Already proved in Lean

Assume only the two hypotheses

1. \(\phi\) is proper;
2. \(\phi\) is a local homeomorphism.

From these, Lean already proves:

1. \(\phi\) is a finite-sheeted covering of constant degree \(d\ge 1\), i.e.
   \[
   \#\,\phi^{-1}(w)=d \qquad \text{for all } w\in\Omega;
   \]
2. for some \(R>4\), the loop
   \[
   \Gamma_R(t)=\phi(Re^{2\pi i t})
   \]
   is freely homotopic in \(\Omega\) to the positive standard circle
   \[
   C_R(t)=Re^{2\pi i t}.
   \]

No further analytic estimate is missing.

## Exact theorem to prove

Prove that these two facts force \(d=1\). Equivalently, prove
\[
\exists\,w_0\in\Omega,\qquad \#\,\phi^{-1}(w_0)=1.
\]

## Standard topology statement that should suffice

If \(p:A\to B\) is a connected \(d\)-sheeted covering between annuli, then under
the identifications \(\pi_1(A)\cong\mathbf Z\) and \(\pi_1(B)\cong\mathbf Z\),
the induced map \(p_*:\pi_1(A)\to\pi_1(B)\) is multiplication by \(\pm d\).

Applying this to \(\phi\), the homotopy class of \(\Gamma_R\) must be
\(\pm d\) times the positive generator of \(\pi_1(\Omega)\). But the formalized
free homotopy gives \([\Gamma_R]=[C_R]\), and \(C_R\) is the positive generator.
Hence \(\pm d=1\), so \(d=1\).

## Exact Lean target

The unresolved abstract topology theorem is:

```lean
def RestrictedAnnulusCoveringDegreeOneStepTwo : Prop :=
  ∀ (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))),
      (∃ R : ℝ, ∃ hR : 4 < R,
        Nonempty
          (ContinuousMap.Homotopy
            (exteriorCircleLoopTwo R hR)
            ((ContinuousMap.mk _ h_local.continuous).comp
              (outsideOpenCircleLoopTwo R hR)))) →
        RestrictedAsymptoticWindingDegreeOneTwo
```

The Bottcher-specific bridge is now derived constructively from this theorem and
the already formalized large-circle homotopy:

```lean
def RestrictedAsymptoticWindingBridgeTwo : Prop :=
  ∀ (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))),
      RestrictedAsymptoticWindingDegreeOneTwo
```

where

```lean
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1
```

The current root axiom is exactly

```lean
MLC.restrictedWindingKernelTwo :
  DirectProperLocalWitnessTwo ∧
    Mlc.Bottcher.DegreeOne.RestrictedAnnulusCoveringDegreeOneStepTwo
```
