# Single remaining expert task: basin-valued Böttcher/external-ray package at \(c=2\)

Let
\[
f_2(z)=z^2+2,
\qquad
\mathcal B_\infty(2)=\{z\in\mathbb C: f_2^{\circ n}(z)\to\infty\},
\qquad
\Omega=\{w\in\mathbb C:|w|>1\},
\]
and let
\[
V_2=\{z\in\mathbb C:|z|>4\}.
\]

The discarded global-oddness route is impossible because \(0\in\mathcal
B_\infty(2)\). Therefore the remaining mathematical work should be posed as one
single task, not as several disconnected subproblems.

---

## Expert task

Prove the following theorem.

### Theorem (basin-valued normalized Böttcher/external-ray package at \(c=2\)).
There exist maps
\[
\phi_2:\mathcal B_\infty(2)\to\Omega,
\qquad
\Psi_2:\Omega\to\mathcal B_\infty(2)
\]
such that:

\[
\phi_2(f_2(z))=\phi_2(z)^2
\qquad\text{for all }z\in\mathcal B_\infty(2),
\]

\[
\frac{\phi_2(z)}{z}\to 1
\qquad(z\to\infty \text{ in } \mathcal B_\infty(2)),
\]

\[
\phi_2(\Psi_2(w))=w
\qquad\text{for all }w\in\Omega,
\]

and

\[
\Psi_2(\phi_2(z))=z
\qquad\text{for all }z\in V_2.
\]

In addition, the proof must establish the following theorem-facing consequences.

### Consequence A (modulus / Green function).
For all \(z\in\mathcal B_\infty(2)\),
\[
|\phi_2(z)|=e^{G_2(z)},
\]
where \(G_2\) is the Green function of \(f_2\).

### Consequence B (outside-open injectivity).
The restriction
\[
\phi_2|_{V_2}:V_2\to\Omega
\]
is injective.

### Consequence C (exterior surjectivity).
The map \(\phi_2\) is surjective onto \(\Omega\):
\[
\phi_2(\mathcal B_\infty(2))=\Omega.
\]

### Consequence D (ray formula on the outside-open region).
For every \(u\in\mathbb C\) with \(|u|=1\) and every \(\rho>4\),
\[
\phi_2(\rho u)=u\,e^{G_2(\rho u)}.
\]

---

## Admissible proof constraints

The proof must **not** use any identity of the form
\[
\phi_2(-z)=-\phi_2(z)
\qquad (z\in\mathcal B_\infty(2)),
\]
because this is impossible when \(0\in\mathcal B_\infty(2)\).

Instead, the proof should proceed by local/exterior arguments only, for example:

1. construct the normalized Böttcher coordinate on a simply connected exterior
   region and propagate it along \(\mathcal B_\infty(2)\) by analytic continuation;
2. prove injectivity on \(V_2\) by eventual injectivity near \(\infty\) plus
   pullback under \(f_2\), using only local oddness on regions that avoid \(0\);
3. prove surjectivity onto \(\Omega\) by backward lifting of roots from a
   neighborhood of \(\infty\), again avoiding any impossible global oddness
   claim at the critical point.

---

## Why this is the only remaining mathematical task

If the theorem above is proved and the formal interface is changed so that
`bottcher_map` is basin-valued (or bundled with the condition
\(z\in\mathcal B_\infty(2)\)), then:

1. the current axiom `MLC.Quadratic.bottcher_coordinate_data` is replaced by the
   theorem-facing existence of \(\phi_2\);
2. the current axiom `MLC.Quadratic.external_ray_map_exists_two` is replaced by
   the theorem-facing existence of \(\Psi_2\);
3. the current axiom `MLC.bottcher_map_eq_one_not_mem_K_two` disappears
   automatically, because it is a pure artefact of evaluating a totalized map on
   \(K(2)\), whereas the genuine Böttcher coordinate is only canonical on
   \(\mathcal B_\infty(2)\).

So the expert should treat the entire remaining job as exactly one theorem:

\[
\boxed{\text{Construct the basin-valued normalized Böttcher coordinate at }c=2
\text{ together with its exterior inverse package.}}
\]
