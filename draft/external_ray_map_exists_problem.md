# Expert handoff: abstract annulus degree-one step at `c = 2`

Let
\[
V=\{z\in\mathbf C:\ |z|>4\},\qquad \Omega=\{w\in\mathbf C:\ |w|>1\}.
\]
Let \(\phi:V\to\Omega\) be the restricted outside Böttcher map for \(f(z)=z^2+2\).

## Input already formalized in Lean

Assume:

1. \(\phi\) is proper;
2. \(\phi\) is a local homeomorphism;
3. for some \(R>4\), the loop
   \[
   \Gamma_R(t)=\phi(Re^{2\pi i t})
   \]
   is freely homotopic in \(\Omega\) to the positive standard circle
   \[
   C_R(t)=Re^{2\pi i t}.
   \]

Lean already derives from (1) and (2) that \(\phi\) is a finite-sheeted covering
of constant degree \(d\ge 1\):
\[
\#\,\phi^{-1}(w)=d \qquad \text{for all } w\in\Omega.
\]

## Exact problem

Prove that \(d=1\). Equivalently,
\[
\exists\,w_0\in\Omega,\qquad \#\,\phi^{-1}(w_0)=1.
\]

## Standard theorem that should suffice

If \(p:A\to B\) is a connected \(d\)-sheeted covering between annuli, then under
the identifications \(\pi_1(A)\cong\mathbf Z\) and \(\pi_1(B)\cong\mathbf Z\),
the induced map \(p_*:\pi_1(A)\to\pi_1(B)\) is multiplication by \(\pm d\).

Applied to \(\phi\), this says that \([\Gamma_R]\in\pi_1(\Omega)\) must equal
\(\pm d\) times the positive generator. But the formalized free homotopy gives
\([\Gamma_R]=[C_R]\), and \(C_R\) is the positive generator. Hence \(\pm d=1\),
so \(d=1\).

## Exact Lean target

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

The current root axiom is exactly

```lean
MLC.restrictedWindingKernelTwo :
  DirectProperLocalWitnessTwo ∧
    Mlc.Bottcher.DegreeOne.RestrictedAnnulusCoveringDegreeOneStepTwo
```
