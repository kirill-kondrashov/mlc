# MLC: a research formalization in Lean 4

[Interactive dependency graph](https://kirill-kondrashov.github.io/mlc/mlc_conjecture/) ·
[Programme, PDF](study/programme.pdf) · [Current task](study/research_passport.md)

The active root is a **checked conditional reduction of MLC to Dudko's
Problems 4.3 and 4.4** from
[arXiv:2512.24171 §4](https://arxiv.org/abs/2512.24171):
return estimates → divergent budget → shrinking connected parameter pieces
→ pointwise local connectivity → global MLC after virtual-Molecule
interpolation.

`RootInput` has exactly two explicit inputs:

* `Problem43PseudoSiegelAPrioriBoundsData`: a candidate return system together
  with its pseudo-Siegel/near-degenerate analytic realization;
* `Problem44VirtualMoleculeData`: the interpolation statement that leaves no
  uncovered boundary parameter outside that system.

The arguments represented by §§4.1–4.4 are assembled in the checked M1
reduction. Problem 4.4 is used only to discharge the candidate system's global
coverage theorem; the general connected-basis and local-connectivity theorems
are proved. Neither open problem is hidden as an axiom: they are fields of
`RootInput`.

**Scope.** The numerical and topological reductions are proved. The candidate
system, its analytic realization, and completion over the virtual Molecule are
packaged as the two open research inputs. MLC remains conditional on those
inputs.

| Step | Canonical source |
| --- | --- |
| Degree loss, distortion, divergent budget | [ReturnBudget.lean](Mlc/Research/ReturnBudget.lean) |
| Separation estimate, shrinking, connected basis | [ParameterGeometry.lean](Mlc/Research/ParameterGeometry.lean) |
| Checked M1 reduction | [Programme.lean](Mlc/Research/Programme.lean) |
| Dudko Problems 4.3 and 4.4 | [CategoricalResidual.lean](Mlc/CategoricalResidual.lean) |
| Root | [CategoricalRoot.lean](Mlc/CategoricalRoot.lean), [Core.lean](Mlc/Core.lean) |
| Exact formulation and remaining tasks | [M1 note](study/research/MLC_bridge.md), [PDF](study/mlc_bridge.pdf) |

The graph is extracted from elaborated Lean types and proofs. Interactive
version: `make serve`. Its red open nodes are
`Problem43PseudoSiegelAPrioriBoundsData` and
`Problem44VirtualMoleculeData`; all other reachable theorem nodes are checked.
The audit permits only `propext`, `Quot.sound`, and `Classical.choice`.
There are no project axioms or `sorry`.

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
