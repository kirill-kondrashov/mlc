# Mandelbrot Local Connectivity in Lean 4

A Lean 4 reduction of the local connectivity of the Mandelbrot set (MLC) to operational forms of the
two open problems that Dudko states at the end of [arXiv:2512.24171](https://arxiv.org/abs/2512.24171)
(§4):

```lean
MLC.Problem43PseudoSiegelAPrioriBoundsData →
MLC.Problem44VirtualMoleculeData p43 →
LocallyConnectedSpace MLC.mandelbrotSet
```

These two inputs are the only open ones, and the proof uses only the axioms listed below. The
survey states that Problems 4.3 and 4.4, together with the arguments of §4.1–§4.4, should imply MLC,
and it does not state the problems in this form; that a solution of the problems provides the two
inputs is the reading proposed here (see [`Mlc/Dudko.lean`](Mlc/Dudko.lean)).
[`Mlc/ProgrammeRoot.lean`](Mlc/ProgrammeRoot.lean) splits the inputs into a tree of statements
(hypotheses, each with its source and an attack plan in the roadmap).

- [Progress report (PDF)](docs/mlc_progress.pdf): what is proved, the numbered and dated updates,
  the map of the certified regions
- [Interactive proof spine](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/)
- [Roadmap](ROADMAP.md): the programme tree, the sources, the attack plans
- [Scripts](scripts/README.md) and [continuous integration](docs/ci.md)

## Build and check

```bash
make build
make check
make graphs       # the proof spine and the progress page, in site/
make report-pdf   # docs/mlc_progress.pdf
```

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
```

Lean 4.28.0; the scripts use Python 3.12 (`pip install -r scripts/requirements.txt` for the map).
