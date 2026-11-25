# Mandelbrot Local Connectivity in Lean 4

[Interactive dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

This repository contains the active Lean reduction of Mandelbrot local
connectedness to the two open problems identified by Dudko at the end of
[arXiv:2512.24171 §4](https://arxiv.org/abs/2512.24171):

```lean
MLC.Problem43PseudoSiegelAPrioriBoundsData →
MLC.Problem44VirtualMoleculeData p43 →
LocallyConnectedSpace MLC.mandelbrotSet
```

`MLC.RootInput` has exactly those two fields. Problem 4.4 is represented by
the Kahn--Dudko--Lyubich virtual-Julia programme: Cantor small Julia sets,
partially invariant connected hulls in `J_c`, first-return prefixes of the
critical orbit, phase--parameter realization, a dynamical separation budget,
and its proved transfer to connected parameter nests. The remaining
interpolation obligation is to supply these a priori controls at every
uncovered boundary parameter.

Every declaration in `Mlc/` is required by the rooted dependency graph. The
generator fails if a local declaration becomes disconnected or if an open
frontier other than Problems 4.3 and 4.4 is exposed.

| Purpose | Source |
| --- | --- |
| Return-budget arithmetic | [ReturnBudget.lean](Mlc/Research/ReturnBudget.lean) |
| Connected parameter nests | [ParameterGeometry.lean](Mlc/Research/ParameterGeometry.lean) |
| Candidate-system reduction | [Programme.lean](Mlc/Research/Programme.lean) |
| Filled Julia compactness and connectedness | [FilledJuliaConnected.lean](Mlc/FilledJuliaConnected.lean) |
| Minimal connected hulls | [ConnectedHull.lean](Mlc/Research/ConnectedHull.lean) |
| Virtual Julia sets and a priori transfer | [VirtualMolecule.lean](Mlc/Research/VirtualMolecule.lean) |
| Problems 4.3 and 4.4 | [Dudko.lean](Mlc/Dudko.lean) |
| Categorical root | [CategoricalRoot.lean](Mlc/CategoricalRoot.lean) |
| Compatibility root | [Core.lean](Mlc/Core.lean) |

```bash
make build
make check
make graphs
make serve
```

The local graph is served at
`http://127.0.0.1:8000/mlc_conjecture/index.html`.

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
```

Lean 4.28.0; the graph generator and server use Python 3.12 with no external
Python packages.
