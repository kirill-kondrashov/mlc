# Task 54 — Pin genuine finite moving parameter window

## Outcome

Performed the feasibility audit requested by the prompt and pinned the smallest
honest finite moving parameter window currently supported by checked repository
data.

## Audit result

### What is available

The repository already contains:
- `Molecule.BMolParameterFamily` with a concrete parameter domain `parameterSet`,
- `Mlc.AnalyticQuadraticLikeFamilyCore` with:
  - `parameterSet : Set ℂ`,
  - `isOpen_parameterSet : IsOpen parameterSet`,
  - fiberwise `GenuineBMol` data over that domain.

So there **is** a checked finite-level moving parameter window candidate:

> the parameter domain of a supplied `BMolParameterFamily` / analytic core.

### What is not available

The repository does **not** currently provide a checked concrete definition of:
- a finite parameter-ray / equipotential graph in the parameter plane,
- a connected component of its complement,
- a proper unfolded equipped quadratic-like family whose parameter domain is
  already connected to the MLC consumer pipeline.

So the preferred source-level candidates from the prompt are not yet
implementable honestly.

## Code landed

In `Mlc/LcAtOfShrink.lean` I added the smallest concrete API only.

### 1. Family-level finite moving window

```lean
def finiteMovingParameterWindow
    (F : BMolParameterFamily ℂ) : Set ℂ :=
  F.parameterSet
```

with elementary lemmas:

```lean
@[simp] lemma mem_finiteMovingParameterWindow_iff ...
@[simp] lemma finiteMovingParameterWindow_eq_parameterSet ...
```

### 2. Analytic-core specialization

```lean
def analyticCoreFiniteMovingParameterWindow
    (F : AnalyticQuadraticLikeFamilyCore) : Set ℂ :=
  F.parameterSet
```

with the direct elementary API:

```lean
@[simp] lemma analyticCoreFiniteMovingParameterWindow_eq ...
lemma isOpen_analyticCoreFiniteMovingParameterWindow ...
lemma mem_analyticCoreFiniteMovingParameterWindow ...
```

This pins one genuine finite-level moving window as an actual `Set ℂ`, proves
ambient openness from checked data, and records basepoint membership from a
supplied parameter-domain membership proof.

## Scope discipline

I did **not** claim any unsupported extra structure:
- no relative Mandelbrot connectedness,
- no nesting/shrinkage,
- no parameter-ray graph component,
- no proper/unfolded-family theorem that the repo does not already contain.

The corrected window/locus interface from Result 53 was left unchanged.

## Smallest next foundation task

The first missing declaration/theorem is an honest concrete provider of a
finite-level moving window beyond plain `parameterSet`, namely one of:

1. a checked parameter-ray/equipotential graph object plus a chosen complement
   component; or
2. a checked proper/unfolded/equipped quadratic-like family whose parameter
   domain is known to be the intended finite parameter window.

Without one of those, the current `parameterSet`-based window is the only honest
finite moving window available.

## Validation

Targeted check passed:

```bash
lake env lean Mlc/LcAtOfShrink.lean
```
