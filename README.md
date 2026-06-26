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

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- Quot.sound
- propext
- Classical.choice
- MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected
- MLC.residualOpenVirtualNearMoleculeAxiom
```

The first three are standard Lean foundations. The checked project frontier is
now reduced to two project axioms:

- `MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`
- `MLC.residualOpenVirtualNearMoleculeAxiom`

Mathematically, the intended end state is still stronger: the first item should
ultimately be discharged from the residual Dudko-2025 package (Problem 4.3,
Interpolation Problem 4.4, and §4.5), leaving only one genuinely open project
axiom. But at the checked root, the standard Böttcher/Green axioms are no
longer part of the axiom frontier.

## Remaining mathematical inputs

### 1. Böttcher coordinate infrastructure

The exterior Böttcher coordinate φ_c and its inverse (external ray map) are
standard objects in holomorphic dynamics. Four axioms encode their fundamental
properties: existence of the inverse on {|w| > 1}, continuity of the extension
to the unit circle, connectivity of the filled Julia set for c ∈ M, and
injectivity of φ_c on the basin of infinity.

These axioms are used to prove Green sublevel connectivity
(`GreenSublevelConnectedHyp`) and the identification
`DynamicalPuzzlePiece c n 0 = GreenSublevel c n` for c ∈ M.

### 2. Parameter puzzle piece connectivity

For each c ∈ M and depth n, the parameter puzzle piece
`ParaPuzzlePieceAt c n ∩ M` is connected.

In Lean the checked root-facing hook is now
`MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected`.

This is the precise remaining non-residual bridge between the current root and
the desired one-axiom end state. Guided by Dudko's 2025 note, the goal is to
show that this para-puzzle connectivity statement follows from the residual
virtual-Molecule package rather than needing any separate standard Böttcher
axioms at the root.

### 3. Virtual Molecule a priori control

Consider a quadratic polynomial whose first quadratic-like renormalization is
primitive. Following Dudko's 2025 notation, this renormalization is encoded by
a primitive copy $M_1 \subset \mathcal M$, together with a chain of satellite
copies

```math
\mathcal M = M^{(0)} \supsetneq M^{(1)} \supsetneq \cdots
\supsetneq M^{(n)} \supsetneq M^{(n+1)}.
```

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

This is the mathematical content represented internally by
`MLC.residualOpenVirtualNearMoleculeAxiom`. In `refs/2512.24171v1.txt`, the
corresponding items are:

1. Problem 4.3: pseudo-Siegel a priori bounds in the remaining unbounded
   satellite quadratic-like cases
2. Interpolation Problem 4.4: a Virtual Molecule version of the
   Near-Degenerate Regime
3. Section 4.5: Virtual near-Molecule Renormalization

Repository policy: no additional project axiom should be introduced beyond this
residual Dudko-2025 package. Any other root-facing axiom should be treated only
as a temporary presentation hook to be eliminated or identified as a direct
consequence of this package.

## How the Lean root uses these inputs

The checked conditional root declaration is in
[`Mlc/MainConjecture.lean`](Mlc/MainConjecture.lean). It reduces MLC
to:

- the parameter puzzle piece connectivity (from `bottcher_onM_hyp` path)
- the virtual Molecule / near-neutral renormalization package

Note: the previous axiom `MLC.unifiedGenuineRootKernelTwo` (asserting a global
Böttcher extension at $c = 2$) has been removed. That statement is
mathematically false: for $c = 2 \notin \mathcal M$ the basin of infinity is
not simply connected (the Julia set is a Cantor set), so no single-valued
holomorphic Böttcher coordinate extending to the full basin can exist. The
motion bridge that consumed it was proved to ignore its input, making the
axiom dead code. See
[`notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb`](notebooks/frontier_plan06_unified_global_bottcher_theorem.ipynb)
for the full analysis.

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
