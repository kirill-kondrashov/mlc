# Task 55 — Audit parameter graph component provider

## Outcome

I performed the requested repository/source audit for a concrete provider of
finite parameter-plane graphs and components of their complements.

## Audit target

The prompt asked whether the repository already supports honest declarations of
the form:

```lean
parameterGraph : ℕ → Set ℂ
parameterOpenPiece : ℕ → ℂ → Set ℂ
```

where:
- `parameterGraph n` is built from finitely many **parameter-plane** rays /
  equipotentials / landing data (or an equivalent checked proper-family
  construction), and
- `parameterOpenPiece n c` is an actual connected component of the complement.

## Result: no concrete provider exists yet

After auditing both `Mlc/` and `refs/`, there is **no checked provider** for a
finite parameter graph or a component of its complement.

### What does exist

1. **Dynamical / exterior Böttcher-side infrastructure**
   - `Mlc/Quadratic/Complex/Bottcher/BottcherRayMap.lean`
   - `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`
   - related Böttcher files

   These concern the existing proxy/external-ray map and parameter-holomorphy of
   a near-infinity Böttcher family, but they do **not** define a genuine
   parameter-plane external coordinate, parameter rays, or finite graph objects.

2. **Abstract moving-family domains**
   - `Molecule.BMolParameterFamily.parameterSet`
   - `Mlc.AnalyticQuadraticLikeFamilyCore.parameterSet`

   These are honest ambient parameter domains, but they are **not** finite
   parapuzzle graphs and do not come with complement components.

3. **Source/reference notes**
   - `refs/Dudko_relevance_external_ray_map_exists.md`
   - various PDFs in `refs/`

   These are strategic references only; they do not supply checked Lean
   declarations implementing parameter graphs/components.

### What does *not* exist

I found no checked Lean declaration for any of the following:
- parameter-plane external coordinate on `ℂ \ MandelbrotSet`,
- parameter rays or parameter equipotentials as sets in `ℂ`,
- finite unions of such objects forming `parameterGraph n`,
- landing/root/tip combinatorics feeding a finite graph,
- `connectedComponentIn`-based complement pieces attached to such a graph,
- a proper/unfolded family theorem already packaged to serve as an equivalent
  finite graph/component provider.

## Exact first blocker

The **first missing parameter-plane declaration** is an honest parameter-plane
external-coordinate / ray provider.

Concretely, the next missing object is something equivalent in strength to:

```lean
parameterExternalRay : Angle → ℝ → ℂ
```

or a set-level version such as

```lean
parameterRay : Angle → Set ℂ
parameterEquipotential : ℝ → Set ℂ
```

with enough checked API to form finite unions and talk about components of their
complements.

Without that, there is no honest route to define

```lean
parameterGraph : ℕ → Set ℂ
```

from finite parameter-ray/equipotential data.

## Smallest honest next task

The smallest next foundation task is:

> Formalize a genuine parameter-plane external coordinate on
> `ℂ \ MandelbrotSet` (or an equivalent set-level parameter-ray/equipotential
> provider), with elementary set-theoretic API sufficient to define finite unions
> of parameter rays/equipotentials.

Only after that would the next task be to define:
- a finite parameter graph,
- the complement open set,
- a chosen connected component containing a base parameter,
- openness / connectedness facts for that component.

## Scope discipline

Per instructions, I made **no source edits**, because no honest provider exists
and the prompt explicitly forbade adding another arbitrary `Set ℂ` shell.

## Validation

No code changes were made, so no build step was needed.
