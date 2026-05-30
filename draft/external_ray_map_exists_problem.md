# Remaining algebraic-topology theorem for `RestrictedAsymptoticWindingDegreeOneTwo`

Let
\[
V=\{z\in\mathbb C:\ |z|>4\},\qquad \Omega=\{w\in\mathbb C:\ |w|>1\}.
\]
Let \(\phi:V\to\Omega\) be the restricted B\"ottcher map for \(f(z)=z^2+2\).

## Already proved in Lean

1. \(\phi\) is a proper local homeomorphism.
2. There exists an integer \(d\ge 1\) such that
   \[
   \#\,\phi^{-1}(w)=d \qquad \forall w\in\Omega.
   \]
3. There exists \(R>4\) such that the loop
   \[
   \Gamma_R(t)=\phi(Re^{2\pi i t}), \qquad t\in[0,1],
   \]
   is freely homotopic in \(\Omega\) to the standard positive circle
   \[
   C_R(t)=Re^{2\pi i t}.
   \]

No analytic work remains.

## Exact problem for the expert

Prove:

> If \(\phi:V\to\Omega\) is a proper local homeomorphism with constant finite
> fiber cardinality \(d\ge 1\), and if for some \(R>4\) the loop
> \(\Gamma_R(t)=\phi(Re^{2\pi i t})\) is freely homotopic in \(\Omega\) to the
> positive generator \(C_R(t)=Re^{2\pi i t}\), then \(d=1\).

Equivalently, prove that \(\phi\) has a singleton fiber:
\[
\exists w_0\in\Omega,\qquad \#\,\phi^{-1}(w_0)=1.
\]

## Expected topology input

Use the standard annulus-covering fact:
\[
\phi_*:\pi_1(V)\cong \mathbb Z \to \pi_1(\Omega)\cong \mathbb Z
\]
is multiplication by \(\pm d\) for a \(d\)-sheeted connected covering.
Hence
\[
[\Gamma_R]=\pm d\,[C_R]\in \pi_1(\Omega).
\]
But the already-formalized free homotopy gives
\[
[\Gamma_R]=[C_R].
\]
Therefore \(\pm d=1\), so \(d=1\).

## Exact Lean target

This is exactly the missing theorem behind

```lean
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1
```

because the constancy of `RestrictedFiberCardTwo` is already formalized.
