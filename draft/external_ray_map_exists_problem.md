# Remaining algebraic-topology problem at `c = 2`

Let
\[
V=\{z\in\mathbf C:\ |z|>4\},\qquad \Omega=\{w\in\mathbf C:\ |w|>1\}.
\]
Let \(\phi:V\to\Omega\) be the restricted outside B\"ottcher map for \(f(z)=z^2+2\).

## What is already formalized

Lean already proves:

1. \(\phi\) is a proper local homeomorphism.
2. Therefore \(\phi\) is a finite-sheeted covering of constant degree: there exists
   \(d\ge 1\) such that
   \[
   \#\,\phi^{-1}(w)=d \qquad \text{for every } w\in\Omega.
   \]
3. For some \(R>4\), the loop
   \[
   \Gamma_R(t)=\phi(Re^{2\pi i t}),\qquad t\in[0,1],
   \]
   is freely homotopic in \(\Omega\) to the positive standard circle
   \[
   C_R(t)=Re^{2\pi i t}.
   \]

No further analytic estimate is missing.

## Exact problem statement

Prove that \(d=1\).

Equivalently, prove:
\[
\exists\,w_0\in\Omega \quad \#\,\phi^{-1}(w_0)=1.
\]

## Intended topology theorem

The needed input is the standard annulus-covering fact:

> If \(p:A\to B\) is a connected \(d\)-sheeted covering between annuli, then under
> the identifications \(\pi_1(A)\cong\mathbf Z\) and \(\pi_1(B)\cong\mathbf Z\),
> the induced map \(p_*:\pi_1(A)\to\pi_1(B)\) is multiplication by \(\pm d\).

Applying this to \(\phi\), the class of \(\Gamma_R\) in \(\pi_1(\Omega)\cong\mathbf Z\)
must be \(\pm d\) times the positive generator. But the formalized free homotopy
already gives
\[
[\Gamma_R]=[C_R],
\]
and \(C_R\) is the positive generator. Hence \(\pm d=1\), so \(d=1\).

## Exact Lean target

This is exactly the unresolved conclusion

```lean
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1
```

The root axiom no longer postulates this conclusion outright. It now postulates
the exact bridge theorem

```lean
def RestrictedAsymptoticWindingBridgeTwo : Prop :=
  ∀ (h_proper : IsProperMap (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ)))
    (h_local : IsLocalHomeomorph (MLC.bottcher_map_outside_open_to_exterior (2 : ℂ))),
      RestrictedAsymptoticWindingDegreeOneTwo
```

so the remaining Lean task is precisely to prove this bridge from the already
formalized covering-degree and large-circle homotopy machinery.

The root kernel is therefore

```lean
MLC.restrictedWindingKernelTwo :
  DirectProperLocalWitnessTwo ∧
    Mlc.Bottcher.DegreeOne.RestrictedAsymptoticWindingBridgeTwo
```
