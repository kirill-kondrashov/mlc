# Mandelbrot Local Connectivity in Lean 4

[Interactive dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

The long-term research plan is recorded in the
[roadmap](ROADMAP.md). The short mathematical status report is maintained as
[`docs/mlc_progress.tex`](docs/mlc_progress.tex); run `make report-pdf` to build it.

## Progress dashboard

The [progress table](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/progress.html)
lists every commit after the merge base with `origin/main`: date and time,
commit, description, the certified resolved share, and the result that raised
it. The resolved share is `100% − μ*(R) / 4π`, where `R` is the set of
parameters of the Mandelbrot set without a proved local-connectivity
certificate; a parameter is resolved when it lies outside `M` or in the
interior of `M`. `0%` means nothing is resolved. A map of `M` marks the
parameters certified by each commit. The same table is in the **Progress** tab
of the interactive graph and in `docs/mlc_progress.tex`.

MLC means `R = ∅`, which gives `100%`. The converse fails: a nonempty `R` of
measure zero also gives `100%`, and the area of `∂M` is itself unknown. The
share is therefore read together with the open root obligations, not as a
proof of completion. A separate formalization-debt proxy gates commits.

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
| Mandelbrot escape and compactness | [MandelbrotCompact.lean](Mlc/MandelbrotCompact.lean) |
| Filled Julia compactness and connectedness | [FilledJuliaConnected.lean](Mlc/FilledJuliaConnected.lean) |
| Minimal connected hulls | [ConnectedHull.lean](Mlc/Research/ConnectedHull.lean) |
| Virtual Julia sets and a priori transfer | [VirtualMolecule.lean](Mlc/Research/VirtualMolecule.lean) |
| Fixed-point ball arithmetic, dyadic grid, area bound | [GridCertificate.lean](Mlc/GridCertificate.lean) |
| Grid parameters and checked count | [GridParams.lean](Mlc/GridParams.lean), [GridCertified.lean](Mlc/GridCertified.lean) |
| Problems 4.3 and 4.4 | [Dudko.lean](Mlc/Dudko.lean) |
| Categorical root | [CategoricalRoot.lean](Mlc/CategoricalRoot.lean) |
| Compatibility root | [Core.lean](Mlc/Core.lean) |

### Kernel-checked area bound

`Mlc/GridCertificate.lean` proves that every dyadic square whose critical-orbit
enclosure (fixed-point ball arithmetic) escapes the disk of radius 2, or traps
the orbit in a periodic invariant disk, lies outside `M` or inside `M`; the
unresolved finest cells therefore cover `M ∖ int M`, and the same count bounds
the area of every residual set by `unresolved_volume_le_grid`. The upper
half-plane is classified and the lower half follows by conjugation symmetry.
The count is checked by kernel reduction (`decide +kernel`, no `native_decide`).
The expensive root squares are checked in independent generated modules
`Mlc/GridTiles/Part*.lean`, which Lake builds in parallel; regenerate them with
`python3 scripts/generate_grid_tiles.py` after changing `Mlc/GridParams.lean`.
A full check takes roughly 13 CPU minutes and 3--4 GB of memory per module.

```bash
make build
make check
make install-hooks
make graphs
make serve
make report-pdf
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
