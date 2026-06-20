# PLAN 05: Restricted asymptotic winding degree one at `c = 2`

**Status:** PARKED / AUXILIARY  
**Frontier role:** downstream auxiliary route after the genuine global Bottcher package exists  
**Primary formal hooks:** `Mlc/Quadratic/Complex/Bottcher/DegreeOneInj.lean`, `Mlc/MainConjecture.lean`

---

## Role of this plan now

This plan is no longer the first live attack on the root axiom.

The checked frontier has moved upstream to the theorem-facing genuine Bottcher
package recorded in `PLAN_06_global_bottcher_package.md`. In particular, the
statement below assumes a genuine normalized Bottcher coordinate already exists.

So this plan should be treated as:

1. an auxiliary downstream route for proving outside-open injectivity from
   degree-one covering data,
2. a possible alternate proof of the injectivity clause in the inverse package,
3. not the current first blocker to eliminating `MLC.basinExternalRayKernelTwo`.

---

## Standalone problem statement for a human expert

Let

$$
f(z)=z^2+2,
$$

and let $$\phi$$ be the normalized Bottcher coordinate of $$f$$ on the basin
of infinity, normalized by

$$
\phi(f(z))=\phi(z)^2,
\qquad
\lim_{z\to\infty}\frac{\phi(z)}{z}=1.
$$

Set

$$
V=\{z\in\mathbb C:\ |z|>4\},
\qquad
\Omega=\{w\in\mathbb C:\ |w|>1\}.
$$

Consider the restricted map

$$
\phi|_V : V \to \Omega.
$$

### Exact theorem requested

Prove that if $$\phi|_V$$ is a proper local homeomorphism, then

$$
\exists\,w_0\in\Omega\quad\text{such that}\quad \#\,(\phi|_V)^{-1}(w_0)=1.
$$

Any stronger theorem is fully acceptable, especially:

1. $$\phi|_V$$ has covering degree $$1$$;
2. $$\phi|_V$$ is injective;
3. $$\phi|_V : V \to \Omega$$ is a homeomorphism.

### Intended proof shape

The expected proof is the standard degree-one covering argument:

1. proper local homeomorphism $$\Rightarrow$$ finite-sheeted covering of some
   degree $$d\ge 1$$;
2. therefore every fiber has cardinality $$d$$;
3. for large $$R$$, the loop
   $$
   \Gamma_R(t)=\phi(Re^{it})
   $$
   has winding number $$1$$ around $$0$$, because
   $$
   \phi(z)=z(1+\varepsilon(z)),\qquad \varepsilon(z)\to 0,
   $$
   so $$\Gamma_R$$ is homotopic in $$\Omega$$ to the standard circle
   $$t\mapsto Re^{it}$$;
4. for a $$d$$-sheeted covering $$V\to\Omega$$, that winding number must equal
   $$\pm d$$;
5. hence $$d=1$$.

### Why this is no longer the first formal gap

The Lean development has already formalized the following:

1. from properness + local homeomorphy of the restricted map, the fiber
   cardinality is constant on $$\Omega$$;
2. from one singleton fiber, the code already derives injectivity on $$V$$;
3. from injectivity on $$V$$ plus the already-wired surjectivity bridge, the
   code already derives `ExternalRayMapData (2)` and then the root MLC theorem.

But this route is now downstream of the genuine-coordinate plan:

1. the repository still first needs an actual theorem constructing the genuine
   global coordinate and its inverse-package consequences;
2. only after that theorem-facing package exists does the present winding-degree
   route become relevant as an auxiliary way to prove injectivity on $$V$$.

### Exact formal placeholder

The theorem needed by the current code is:

```lean
def RestrictedAsymptoticWindingDegreeOneTwo : Prop :=
  ∃ y : {w : ℂ // 1 < ‖w‖}, RestrictedFiberCardTwo y = 1
```

where `RestrictedFiberCardTwo y` is the cardinality of the fiber of the
restricted map

```lean
MLC.proxy_bottcher_map_outside_open_to_exterior (2 : ℂ) :
  {z : ℂ // ‖z‖ > 4} → {w : ℂ // 1 < ‖w‖}
```

under the identification $$\|2\|+2=4$$.

---

## Success criterion

Produce a rigorous proof of the theorem above, or of any stronger theorem that
immediately implies it, **after** the upstream global Bottcher package from
`PLAN_06_global_bottcher_package.md` is available.
