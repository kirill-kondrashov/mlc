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

Let $f_c : \mathbb C \to \mathbb C$ be the
[quadratic polynomial](https://en.wikipedia.org/wiki/Quadratic_polynomial)
$f_c(z) = z^2 + c$. The
[Mandelbrot set](https://en.wikipedia.org/wiki/Mandelbrot_set) is

```math
\mathcal M = \{c \in \mathbb C : (f_c^n(0))_{n \ge 0} \text{ is bounded}\}.
```

For a [topological space](https://en.wikipedia.org/wiki/Topological_space) $X$
and a point $x \in X$,
[local connectivity](https://en.wikipedia.org/wiki/Locally_connected_space) at
$x$ means that every neighbourhood $U$ of $x$ contains a connected
neighbourhood $V$ of $x$ with $V \subset U$. In Lean this is the
predicate `MLC.LocallyConnectedAt`.

The conjectural statement formalized at the root is:

**Conjecture (MLC).** The Mandelbrot set $\mathcal M$, with the subspace
topology inherited from $\mathbb C$, is locally connected.

In Lean this conditional declaration is `MLC.mlc_conjecture`; it has type
`LocallyConnectedSpace MLC.mandelbrotSet`.

The formal statement of the conjecture is based on DeepMind's
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
repository, specifically
[`FormalConjectures/Wikipedia/Mandelbrot.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mandelbrot.lean).

## Checked Lean status

Run:

```bash
make build
make check
```

The root declaration is sorry-free. The current `make check` axiom frontier is:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.paraPuzzleTransportWitnessHyp_of_residualOpenVirtualNearMolecule
- MLC.residualOpenVirtualNearMoleculeAxiom
```

The first three are standard Lean foundations. The remaining project axioms are:

- `MLC.paraPuzzleTransportWitnessHyp_of_residualOpenVirtualNearMolecule`:
  assuming the residual Dudko package below, one obtains a parameter-puzzle
  transport witness on `M`. Concretely, for every parameter puzzle piece
  `ParaPuzzlePieceAt c n` with `c ∈ M`, there is a holomorphic motion package on
  a neighborhood of `c` whose preserved fibers identify
  `ParaPuzzlePieceAt c n ∩ M` with a connected subset of the parameter line.
  This is the exact bridge consumed by the checked root.
- `MLC.residualOpenVirtualNearMoleculeAxiom`: Dudko-2025's remaining open input,
  bundled as a single residual package consisting of
  1. **Problem 4.3**: pseudo-Siegel a priori bounds in the remaining unbounded
     satellite quadratic-like cases;
  2. **Interpolation Problem 4.4**: a Virtual Molecule version of the
     Near-Degenerate Regime;
  3. the deduction promised in the last paragraph of `refs/2512.24171v1.txt`:
     Problems 4.3 and 4.4, together with the arguments of §§4.1–4.5, imply the
     Track-1/Track-2 infinite-renormalization package and the transport witness
     interface used at the root.

These formulations specify exactly what remains unproved in this repository,
without relying on internal file names or implementation details.

## Remaining open mathematical problems

The repository is intended to isolate the remaining unproved mathematical
content as explicit statements. For a first reading, the open problems are the
following.

### 1. Parameter-puzzle fiber connectedness from holomorphic transport

For every parameter $c \in \mathcal M$ and every puzzle depth $n \ge 0$, let
$P_n(c)$ denote the corresponding parameter puzzle piece. One needs a theorem
asserting that the boundary of $P_n(c)$ admits a local holomorphic motion in
parameter space whose preserved fibers imply that

```math
P_n(c) \cap \mathcal M
```

is connected.

This is the connectedness input used in the finite-branch/Yoccoz argument. In
formal terms, the repository presently leaves this statement at the root in the
form of the bridge axiom
`MLC.paraPuzzleTransportWitnessHyp_of_residualOpenVirtualNearMolecule`.

### 2. Problem 4.3 of Dudko (2025): pseudo-Siegel a priori bounds in the remaining unbounded satellite quadratic-like cases

One needs uniform a priori bounds in the remaining unbounded satellite
quadratic-like renormalization cases. Concretely, this means uniform positive
lower bounds for the conformal moduli of the annuli controlling the relevant
quadratic-like renormalizations in the pseudo-Siegel/unbounded satellite
regime.

Equivalently, the renormalization geometry in these remaining unbounded
satellite cases must stay in a precompact class and not degenerate at small
scales.

### 3. Interpolation Problem 4.4 of Dudko (2025): a Virtual Molecule version of the Near-Degenerate Regime

Assume the first quadratic-like renormalization of $f$ is primitive, encoded by
a primitive copy $M_1 \subset \mathcal M$, and let

```math
\mathcal M = M^{(0)} \supsetneq M^{(1)} \supsetneq \cdots
\supsetneq M^{(n)} \supsetneq M^{(n+1)}
```

be the canonical chain of maximal satellite copies described in §4.5 of
Dudko's note. The virtual Molecule regime is the interval of parameter scales
between the ambient copy $\mathcal M$ and $M^{(n)}$, i.e. the scales not
controlled by the puzzle levels used between $M^{(n)}$ and $M_1$.

The required statement is that the Near-Degenerate Regime extends to this
virtual Molecule setting, with uniform geometric control across those
intermediate scales, including the virtual bounded-type satellite and virtual
near-neutral subcases.

### 4. Deduction from §§4.1–4.5 to the MLC route formalized here

The final remaining deduction is the theorem asserted in the last paragraph of
`refs/2512.24171v1.txt`: Problems 4.3 and 4.4, together with the arguments of
§§4.1–4.5, imply the full MLC route formalized in this repository.

Concretely, this means deriving from those inputs both:

1. the infinite-renormalization package used by the root proof; and
2. the parameter-puzzle transport statement in item 1 above.

Repository policy: these Dudko-style residual statements are the only allowed
remaining project-level mathematical assumptions. Any bridge statement used by
the checked root should ultimately be discharged from them rather than retained
as an independent mathematical assumption.

## How the Lean root uses these inputs

The checked conditional root declaration is in
[`Mlc/MainConjecture.lean`](Mlc/MainConjecture.lean). It reduces MLC
to:

- the parameter puzzle transport witness
- the virtual Molecule / near-neutral renormalization package

The repository also records an excluded route: the statement previously named
`MLC.unifiedGenuineRootKernelTwo`, asserting a global Böttcher extension at
$c = 2$, is mathematically false. For $c = 2 \notin \mathcal M$ the basin of
infinity is not simply connected (the Julia set is a Cantor set), so no
single-valued holomorphic Böttcher coordinate extending to the full basin can
exist. The corresponding motion bridge was shown not to use this input. See
[`notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb`](notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb)
for the analysis.

The dependency graph visualizes this reduction:

```bash
make graphs
```

## Repository entry points

- Root declaration: [`MLC.mlc_conjecture`](Mlc/MainConjecture.lean#L4593-L4604)
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
