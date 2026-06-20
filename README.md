# Mandelbrot Local Connectivity (MLC) in Lean 4

[![build](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/kirill-kondrashov/mlc/actions/workflows/lean_action_ci.yml)

[Dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

> [!IMPORTANT]
> This repository is an experimental Lean 4 formalization attempt, not a
> completed proof of the Mandelbrot local connectivity conjecture. It formalizes
> reductions, definitions, and proof obligations from the current literature
> corpus, with remaining mathematical inputs isolated as explicit project
> axioms. Its intended use is to provide infrastructure for automatically
> checking a proof of MLC when a complete proof appears in the literature.

## Mathematical statement and notation

Let $f_c : \mathbb C \to \mathbb C$ be the quadratic polynomial
$f_c(z) = z^2 + c$. The Mandelbrot set is
$$
  \mathcal M = \{c \in \mathbb C : (f_c^n(0))_{n \ge 0} \text{ is bounded}\}.
$$

For a topological space $X$ and a point $x \in X$, local connectivity at
$x$ means that every neighbourhood $U$ of $x$ contains a connected
neighbourhood $V$ of $x$ with $V \subset U$. In Lean this is the
predicate `MLC.LocallyConnectedAt`.

The conjectural statement formalized at the root is:

**Conjecture (MLC).** The Mandelbrot set $\mathcal M$, with the subspace
topology inherited from $\mathbb C$, is locally connected.

In Lean this conditional declaration is `MLC.mlc_conjecture`; it has type
`LocallyConnectedSpace MLC.mandelbrotSet`.

## Checked Lean status

Run:

```bash
make build
make check
```

The root declaration is sorry-free. The current `make check` axiom frontier is:

```text
Quot.sound
propext
Classical.choice
MLC.residualOpenVirtualNearMoleculeAxiom
MLC.unifiedGenuineRootKernelTwo
```

The first three are standard Lean foundations. The project frontier consists
of the last two axioms.

## Remaining mathematical inputs

### 1. Global Böttcher extension at $c = 2$

Let $f_2(z) = z^2 + 2$, and let
$$
  A_\infty(f_2) = \{z \in \mathbb C : |f_2^n(z)| \to \infty\}
$$
be the basin of infinity. Let $G_2$ denote the Green function of $f_2$.
Near infinity there is a normalized Böttcher map $\phi$ satisfying
$$
  \phi(f_2(z)) = \phi(z)^2, \qquad \phi(z) / z \to 1 \quad (z \to \infty).
$$

**Theorem (global Böttcher extension at $c = 2$).** There is a map
$\Phi : \mathbb C \to \mathbb C$, holomorphic on $A_\infty(f_2)$, such
that:

1. $\Phi(f_2(z)) = \Phi(z)^2$ for all $z \in A_\infty(f_2)$;
2. $z \in A_\infty(f_2)$ if and only if $|\Phi(z)| > 1$;
3. $|\Phi(z)| = \exp(G_2(z))$;
4. $\Phi(z) / z \to 1$ as $z \to \infty$;
5. on a sufficiently large exterior region, $\Phi$ agrees with the
   normalized near-infinity Böttcher coordinate.

This is the mathematical content represented at the root by
`MLC.unifiedGenuineRootKernelTwo`. The relevant Lean entry points are:

- [`Quadratic.genuineBottcherNearInfinityDataFor_logSeriesBottcherApprox`](Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean#L130-L145)
- [`MLC.MainProof.mlc_conjecture_of_principalPullbackCoherentData_two`](Mlc/MainConjecture.lean#L2152-L2173)
- [`MLC.MainProof.mlc_conjecture_of_unifiedGlobalBottcherTheorem_two`](Mlc/MainConjecture.lean#L2195-L2208)

### 2. Virtual Molecule a priori control

Consider a quadratic polynomial whose first quadratic-like renormalization is
primitive. Following Dudko's 2025 notation, this renormalization is encoded by
a primitive copy $M_1 \subset \mathcal M$, together with a chain of satellite
copies
$$
  \mathcal M = M^{(0)} \supsetneq M^{(1)} \supsetneq \cdots
  \supsetneq M^{(n)} \supsetneq M^{(n+1)}.
$$
Here each $M^{(j+1)}$ is a maximal satellite subcopy of $M^{(j)}$. The
virtual Molecule regime is the range of parameter scales between the ambient
copy $\mathcal M$ and $M^{(n)}$; in Dudko's formulation, this is the range
not controlled by the puzzle levels used between $M^{(n)}$ and $M_1$.

**Theorem (virtual Molecule a priori control).** Uniform a priori bounds hold
in the remaining unbounded satellite quadratic-like cases, and the
near-degenerate regime extends to the virtual Molecule setting above. Here
“a priori bounds” means uniform positive lower bounds for the conformal moduli
of the annuli controlling the corresponding renormalization geometry.
Equivalently, there is uniform geometric control of the relevant
renormalization scales along the chain of satellite copies, including the
virtual bounded-type satellite and virtual near-neutral subcases described in
Section 4.5 of Dudko's note.

This is the mathematical content represented at the root by
`MLC.residualOpenVirtualNearMoleculeAxiom`. In `refs/2512.24171v1.txt`, the
corresponding items are:

1. Problem 4.3: pseudo-Siegel a priori bounds in the remaining unbounded
   satellite quadratic-like cases
2. Interpolation Problem 4.4: a Virtual Molecule version of the
   Near-Degenerate Regime
3. Section 4.5: Virtual near-Molecule Renormalization

## How the Lean root uses these inputs

The checked conditional root declaration is in
[`Mlc/MainConjecture.lean`](Mlc/MainConjecture.lean#L4515-L4523). It reduces MLC
to the two mathematical inputs above:

- the global Böttcher extension package at $c = 2$
- the virtual Molecule / near-neutral renormalization package

The dependency graph visualizes this reduction:

```bash
make graphs
```

## Repository entry points

- Root theorem: [`MLC.mlc_conjecture`](Mlc/MainConjecture.lean#L4515-L4523)
- Root axiom check: [`check_axioms.lean`](check_axioms.lean)
- Dependency graph generator:
  [`scripts/generate_dependency_graph_site.py`](scripts/generate_dependency_graph_site.py)
- Global Böttcher plan: [`plan/PLAN_06_global_bottcher_package.md`](plan/PLAN_06_global_bottcher_package.md)
- Monodromy plan: [`plan/PLAN_08_analytic_continuation_monodromy.md`](plan/PLAN_08_analytic_continuation_monodromy.md)
- Actual overlap plan: [`plan/PLAN_09_actual_overlap_neighborhoods.md`](plan/PLAN_09_actual_overlap_neighborhoods.md)

## Notebooks

```bash
make notebook
```

This renders `notebooks/` to static HTML and serves them locally on
`127.0.0.1:8888`.

The main frontier notebook is
[`notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb`](notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb).

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- [yoccoz-theorem](https://github.com/kirill-kondrashov/yoccoz-theorem)
- [molecule-conjecture](https://github.com/kirill-kondrashov/molecule-conjecture)

Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
