# Mandelbrot Local Connectivity in Lean 4

[Interactive proof spine](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)

The long-term research plan is recorded in the
[roadmap](ROADMAP.md). The short mathematical status report is maintained as
[`docs/mlc_progress.tex`](docs/mlc_progress.tex); run `make report-pdf` to build it.

## Progress dashboard

The [progress table](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/progress.html)
lists every commit after the literature baseline: date and time, commit,
description, the certified resolved share, and the result that raised it. The
baseline is the first commit whose formal root is exactly Dudko's Problems 4.3
and 4.4 (MLC follows from them and both stay open); its row shows the open
problems instead of a percentage. The resolved share is `100% − μ*(R) / 4π`,
where `R` is the set of parameters of the Mandelbrot set without a proved
local-connectivity certificate; a parameter is resolved when it lies outside
`M` or in the interior of `M`. A map of `M` marks the parameters certified by
each commit, one colour per commit, stacked from the newest region at the
bottom to the oldest on top. The same table is in the **Progress** tab of the
interactive graph and in `docs/mlc_progress.tex`.

MLC means `R = ∅`, which gives `100%`. The converse fails: a nonempty `R` of
measure zero also gives `100%`, and the area of `∂M` is itself unknown. The
share is therefore read together with the open root obligations. A separate
formalization-debt proxy gates commits.

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

The graph is drawn as one 2D figure, the proof spine. The spine climbs from the
three kernel axioms at the bottom to the statement of MLC at the top (the head).
Its ten vertebrae are milestone theorems of the library, in an order that the
generator checks against the dependency graph. Every other declaration hangs on
the branch of the lowest vertebra that needs it. The tips of the branches are
the two open problems of the root (red), the targets of Dudko's programme that
are not formalized (amber, dashed: Conjecture 3.6, the area of `∂M`, the virtual
subcases of Problem 4.4), the kernel-checked grid (cyan), and the checked
lemmas (green). Hover a node to light its way to the head, click it for the
statement, the Lean name and its declarations, and use the search to find any
declaration. The bubble on a node counts the declarations that hang on it (its
size grows with the logarithm of the count), the line under a node splits them
into theorems, lemmas, definitions and structures, and the side panel gives the
totals of the library, the share written by hand and the share generated for the
grid certificates, and a table by level of the spine.

| Purpose | Source |
| --- | --- |
| Return-budget arithmetic | [ReturnBudget.lean](Mlc/Research/ReturnBudget.lean) |
| Connected parameter nests | [ParameterGeometry.lean](Mlc/Research/ParameterGeometry.lean) |
| Candidate-system reduction | [Programme.lean](Mlc/Research/Programme.lean) |
| Mandelbrot escape and compactness | [MandelbrotCompact.lean](Mlc/MandelbrotCompact.lean) |
| Filled Julia compactness and connectedness | [FilledJuliaConnected.lean](Mlc/FilledJuliaConnected.lean) |
| Minimal connected hulls | [ConnectedHull.lean](Mlc/Research/ConnectedHull.lean) |
| Virtual Julia sets and a priori transfer | [VirtualMolecule.lean](Mlc/Research/VirtualMolecule.lean) |
| Fixed-point models of the critical orbit and the certificates | [GridDefs.lean](Mlc/GridDefs.lean) |
| Soundness of the models, the certificates and the area bound | [GridCertificate.lean](Mlc/GridCertificate.lean), [GridTMCertificate.lean](Mlc/GridTMCertificate.lean) |
| Checked count and area bound | [GridCertified.lean](Mlc/GridCertified.lean) |
| Problems 4.3 and 4.4 | [Dudko.lean](Mlc/Dudko.lean) |
| Categorical root | [CategoricalRoot.lean](Mlc/CategoricalRoot.lean) |
| Compatibility root | [Core.lean](Mlc/Core.lean) |

### Kernel-checked area bound

`Mlc/GridDefs.lean` defines fixed-point first-order models of the critical
orbit: for every parameter `c` of a square, the `n`-th iterate lies within `e`
of `m + d (c - c₀)`, where `d` is the derivative at the center `c₀`. The model
follows the phases of the derivative and stays sharp where a disk enclosure
grows by large factors. A square lies outside `M` if the model leaves the disk
of radius 2 after `n` steps, and inside `M` if a moving disk centered at the
model returns into itself after `p` steps, so that every parameter of the square
has a bounded critical orbit. A search program, `scripts/grid_hints.lean`, finds
these certificates and writes them as streams of hints. The kernel verifies
every hint (`Sq.certify`) and counts the unresolved finest cells
(`verifyTree`); `Mlc/GridTMCertificate.lean` proves that the verified squares
lie outside `M` or inside `M`. The unresolved finest cells therefore cover
`M ∖ int M`, and the same count bounds the area of every residual set by
`unresolved_volume_le_grid`. The upper half-plane is covered by tiles and the
lower half follows by conjugation symmetry. The count is checked by kernel
reduction (`decide +kernel`, no `native_decide`) in the generated modules
`Mlc/GridTiles/G*.lean`, which import only `Mlc.GridDefs`. A module holds the
tiles of one block of four root squares (a heavy block is split into several
modules) and states the depth at which it counts its unresolved cells, so that
refining some blocks leaves the other modules unchanged and Lake keeps their
builds. The modules are produced by `python3 scripts/refine_grid.py`, which
subdivides cells, and `python3 scripts/coarsen_grid.py`, which replaces the
subdivision of a region by one coarser square with a long inside certificate
(near the border of a hyperbolic component a coarse square costs the kernel the
same per unit of area as a fine one); `python3 scripts/generate_grid_tiles.py`
writes the modules. The depth-11 grid took about 7 CPU
hours (about 40 minutes of wall time on 22 cores); refining the blocks with
`Re c < -3/4` to depth 12 took about 16 minutes more, the blocks with
`-3/4 ≤ Re c < 0` about 24 minutes, and the blocks with `Re c ≥ 0` about 14
minutes. Coarsening the shells changes the modules of most blocks, so the check
of its 6830 modules (20 million steps of the model) is a full rebuild. Refining
the blocks with `Re c < -3/4` to depth 13 checks their 5542 modules again (17
million steps, 8 million of them new) and took about an hour of wall time on 20
cores, and the blocks up to `Re c < -1/8` took about another hour. The
aggregator of 12286 modules needs a thread stack larger than the default of 8 MB
(`weakLeanArgs` in `lakefile.lean`, which stay out of the build trace). A running
module needs about 2.5 GB of memory, and Lake runs as many modules at once as the
machine has cores, so a machine with little memory needs fewer parallel jobs.

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
