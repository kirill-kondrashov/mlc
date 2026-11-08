# MLC: a research formalization in Lean 4

[Interactive dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/) ·
[Programme, PDF](study/programme.pdf) · [Current task](study/research_passport.md)

The active root is a **checked conditional reduction of MLC to M1**:
return estimates → divergent budget → shrinking connected parameter pieces
→ pointwise local connectivity → global MLC under full coverage.

`RootInput` exposes three components: an admissible return system,
its analytic realization, and a separate parameter coverage statement.
The uniform outer buffer is no longer a premise of the main root.
Dudko's open problems are not assumed.

**Scope.** The numerical and topological reductions are proved.
A concrete dynamical admissibility condition must still be selected and
its realization proved. No new parameter outside published classes has
been exhibited. Full coverage is substantially stronger than the first-paper
goal. MLC remains unproved.

| Step | Canonical source |
| --- | --- |
| Degree loss, distortion, divergent budget | [ReturnBudget.lean](Mlc/Research/ReturnBudget.lean) |
| Separation estimate, shrinking, connected basis | [ParameterGeometry.lean](Mlc/Research/ParameterGeometry.lean) |
| M1, coverage, extension beyond a published class | [Programme.lean](Mlc/Research/Programme.lean) |
| Root | [CategoricalRoot.lean](Mlc/CategoricalRoot.lean), [Core.lean](Mlc/Core.lean) |
| Exact formulation and remaining tasks | [M1 note](study/research/MLC_bridge.md), [PDF](study/mlc_bridge.pdf) |

The graph is extracted from elaborated Lean types and proofs;
the current reduction contains 52 theorems. Interactive version: `make serve`.
Open `Realization` and `Coverage` statements are marked as premises of the
conditional root. The audit of every `MLC.Research` theorem permits only
`propext`, `Quot.sound`, and `Classical.choice`. There are no project axioms or `sorry`.

```bash
lake build
make check
make graphs
make -C study
```

Lean 4.28.0; graphs use the existing Python/Poetry site generator; PDFs require Pandoc and XeLaTeX.

Expected `make check` output:

```text
✅ The proof of 'MLC.mlc_conjecture' is free of 'sorry'.
All axioms used:
- propext
- Quot.sound
- Classical.choice
```

The [Pilgrim/B3 package](packages/pilgrim-bisets/README.md) has its own
build and checks. [Earlier approaches and reviews](docs/README.md),
[sources](refs/README.md). Each document has one canonical location;
symbolic links are not used.
