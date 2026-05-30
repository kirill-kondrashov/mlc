# Exact proof for `RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo`

This note proves the exact algebraic-topology theorem behind
`draft/external_ray_map_exists_problem.md`.

## Logical scope check

The draft's expert-language formulation is:

> for a connected finite covering of annuli, if the image of a large outer
> circle is freely homotopic to the positive generator of the target annulus,
> then the covering degree is `1`.

That statement is true and is proved below.

The Lean target now matches this scope: it is quantified in the already-formalized
proper/local-homeomorphism covering context, not as a bare theorem about an
arbitrary continuous map.

The standard loop must also be an exterior circle
\[
C_R(t)=Re^{2\pi i t},\qquad R>4,
\]
not the unit circle \(e^{2\pi i t}\), because the unit circle lies on
\(|w|=1\) and is not contained in \(\Omega=\{|w|>1\}\).

## Theorem

Let
\[
V=\{z\in\mathbb C: |z|>4\},\qquad
\Omega=\{w\in\mathbb C: |w|>1\}.
\]
Let \(\phi:V\to\Omega\) be a connected \(d\)-sheeted covering map, with
\(d\ge 1\). Assume that for some \(R>4\), the loop
\[
\Gamma_R(t)=\phi(Re^{2\pi i t}),\qquad t\in[0,1],
\]
is freely homotopic in \(\Omega\) to the positive exterior circle
\[
C_R(t)=Re^{2\pi i t}.
\]
Then \(d=1\). Consequently every fiber of \(\phi\) has one point, and in
particular
\[
\exists w_0\in\Omega,
\qquad
\#\phi^{-1}(w_0)=1.
\]

## Proof

Fix the basepoint
\[
x_0=R\in V,
\qquad
y_0=\phi(x_0)\in\Omega.
\]
The loop \(C_R\), based at \(x_0\), represents the positive generator of
\(\pi_1(V,x_0)\cong\mathbb Z\). Its image under \(\phi\) is the loop
\(\Gamma_R\), based at \(y_0\), so
\[
[\Gamma_R]=\phi_*([C_R])\in\pi_1(\Omega,y_0).
\]

We use the standard index formula for connected coverings. If \(p:X\to Y\) is
a covering with \(X\) path-connected and \(x\in X\), then
\[
\#p^{-1}(p(x))=[\pi_1(Y,p(x)):p_*(\pi_1(X,x))].
\]
Indeed, lifting loops at \(p(x)\) starting from \(x\) gives a transitive action
of \(\pi_1(Y,p(x))\) on the fiber \(p^{-1}(p(x))\). The stabilizer of \(x\) is
exactly \(p_*(\pi_1(X,x))\), because a loop at \(p(x)\) lifts to a loop at
\(x\) exactly when its homotopy class lies in the image of \(p_*\). Thus the
fiber is naturally identified with the cosets of \(p_*(\pi_1(X,x))\), proving
the formula.

Applying this formula to the connected \(d\)-sheeted covering
\(\phi:V\to\Omega\), the subgroup
\[
\phi_*(\pi_1(V,x_0))\subseteq \pi_1(\Omega,y_0)
\]
has index \(d\). The annulus \(\Omega\) has fundamental group
\(\pi_1(\Omega,y_0)\cong\mathbb Z\), identified by winding number around
\(0\). The only subgroup of \(\mathbb Z\) of index \(d\) is \(d\mathbb Z\).
Since \([C_R]\) generates \(\pi_1(V,x_0)\), the element
\(\phi_*([C_R])=[\Gamma_R]\) generates this index-\(d\) subgroup. Therefore
\[
\operatorname{wind}(\Gamma_R,0)=\varepsilon d
\]
for some sign \(\varepsilon\in\{1,-1\}\).

On the other hand, \(\Gamma_R\) is freely homotopic in \(\Omega\) to \(C_R\) by
hypothesis. Winding number about \(0\) is invariant under free homotopy through
loops in \(\Omega\), since no loop in such a homotopy meets \(0\). Hence
\[
\operatorname{wind}(\Gamma_R,0)=\operatorname{wind}(C_R,0).
\]
The loop \(C_R(t)=Re^{2\pi i t}\) is positively oriented around \(0\), so
\[
\operatorname{wind}(C_R,0)=1.
\]
Combining the two computations gives
\[
\varepsilon d=1.
\]
Because \(d\ge 1\), this forces \(d=1\).

Since \(\phi\) is a \(d\)-sheeted covering, every fiber has cardinality \(d\).
Thus every fiber has cardinality \(1\). Taking, for example, \(w_0=2\in\Omega\)
gives
\[
\#\phi^{-1}(w_0)=1.
\]
This proves the singleton-fiber conclusion.

## Lean-facing conclusion

For the restricted Bottcher map \(\phi=\phi_2|_V\), the repository already
formalizes the proper/local-homeomorphism machinery that supplies the connected
finite-covering interpretation and positive constant degree. The proof above is
therefore the exact remaining generator calculation: the large-circle free
homotopy forces that positive covering degree to be \(1\).

This supplies the mathematical content of
`RestrictedCoveringDegreeOneFromPositiveConstantAndCircleHomotopyTwo` exactly as
it is now stated in Lean: in the already-formalized proper/local covering
context for the restricted outside Böttcher map.
