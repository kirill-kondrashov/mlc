# PLAN 05: Restricted asymptotic winding degree one at `c = 2`

**Status:** ACTIVE  
**Frontier role:** exact remaining mathematical seed for the degree-one route  
**Primary formal hooks:** `Mlc/Quadratic/Complex/Bottcher/DegreeOneInj.lean`, `Mlc/MainConjecture.lean`

---

## Standalone problem statement for a human expert

Let
\[
f(z)=z^2+2,
\]
and let \(\phi\) be the normalized B\"ottcher coordinate of \(f\) on the basin
of infinity, normalized by
\[
\phi(f(z))=\phi(z)^2,
\qquad
\lim_{z\to\infty}\frac{\phi(z)}{z}=1.
\]

Set
\[
V=\{z\in\mathbb C:\ |z|>4\},
\qquad
\Omega=\{w\in\mathbb C:\ |w|>1\}.
\]

Consider the restricted map
\[
\phi|_V : V \to \Omega.
\]

### Exact theorem requested

Prove that if \(\phi|_V\) is a proper local homeomorphism, then
\[
\exists\,w_0\in\Omega\quad\text{such that}\quad \#\,(\phi|_V)^{-1}(w_0)=1.
\]

Any stronger theorem is fully acceptable, especially:

1. \(\phi|_V\) has covering degree \(1\);
2. \(\phi|_V\) is injective;
3. \(\phi|_V : V \to \Omega\) is a homeomorphism.

### Intended proof shape

The expected proof is the standard degree-one covering argument:

1. proper local homeomorphism \(\Rightarrow\) finite-sheeted covering of some
   degree \(d\ge 1\);
2. therefore every fiber has cardinality \(d\);
3. for large \(R\), the loop
   \[
   \Gamma_R(t)=\phi(Re^{it})
   \]
   has winding number \(1\) around \(0\), because
   \[
   \phi(z)=z(1+\varepsilon(z)),\qquad \varepsilon(z)\to 0,
   \]
   so \(\Gamma_R\) is homotopic in \(\Omega\) to the standard circle
   \(t\mapsto Re^{it}\);
4. for a \(d\)-sheeted covering \(V\to\Omega\), that winding number must equal
   \(\pm d\);
5. hence \(d=1\).

### Why this is exactly the current formal gap

The Lean development has already formalized the following:

1. from properness + local homeomorphy of the restricted map, the fiber
   cardinality is constant on \(\Omega\);
2. from one singleton fiber, the code already derives injectivity on \(V\);
3. from injectivity on \(V\) plus the already-wired surjectivity bridge, the
   code already derives `ExternalRayMapData (2)` and then the root MLC theorem.

So the only missing mathematical seed is exactly the existence of one singleton
fiber, equivalently the statement that the restricted map has covering degree
one.

### Exact formal placeholder

The theorem needed by the current code is:

```lean
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1
```

where `RestrictedFiberCardTwo y` is the cardinality of the fiber of the
restricted map

```lean
MLC.bottcher_map_outside_open_to_exterior (2 : ℂ) :
  {z : ℂ // ‖z‖ > 4} → {w : ℂ // 1 < ‖w‖}
```

under the identification \(\|2\|+2=4\).

---

## Success criterion

Produce a rigorous proof of the theorem above, or of any stronger theorem that
immediately implies it.
