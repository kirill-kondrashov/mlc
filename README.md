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

`MLC.RootInput` has exactly those two fields. The checked reduction proves the
numerical return-budget argument, the shrinking connected-nest argument,
pointwise local connectedness, parameter coverage from Problem 4.4, and the
final conditional MLC theorem.

Every declaration in `Mlc/` is required by the rooted dependency graph. The
generator fails if a local declaration becomes disconnected or if an open
frontier other than Problems 4.3 and 4.4 is exposed.

| Purpose | Source |
| --- | --- |
| Return-budget arithmetic | [ReturnBudget.lean](Mlc/Research/ReturnBudget.lean) |
| Connected parameter nests | [ParameterGeometry.lean](Mlc/Research/ParameterGeometry.lean) |
| Candidate-system reduction | [Programme.lean](Mlc/Research/Programme.lean) |
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
