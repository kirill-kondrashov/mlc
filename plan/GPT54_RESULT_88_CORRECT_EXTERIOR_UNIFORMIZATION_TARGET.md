# GPT-5.4 Result 88 — Correct Exterior Uniformization Target

## Outcome

Prompt 88 is completed as an **audit/specification** step.

The earlier external-parameter plan was targeting the wrong topology. After the checked theorem

```lean
mandelbrotSet_compl_isConnected : IsConnected (MandelbrotSetᶜ)
```

the next theorem is **not** ordinary

```lean
IsSimplyConnected (MandelbrotSetᶜ)
```

because the model exterior domain

```lean
{w : ℂ | 1 < ‖w‖}
```

is itself not simply connected as a subspace of `ℂ`. So Prompts 77–82 aimed at the wrong topological target.

The correct Lean-facing target is a **parameter Böttcher / exterior conformal coordinate** on `MandelbrotSetᶜ`, or an equivalent one-point-compactified/spherical formulation, normalized at infinity.

I did **not** edit Lean source, add axioms, or use `sorry`/`admit`.

## Correct target

The right theorem family is one of the following equivalent forms.

### A. Direct parameter Böttcher theorem

Construct a coordinate

```lean
Φ : ℂ → ℂ
```

with conclusions of the shape:

- `DifferentiableOn ℂ Φ (MandelbrotSetᶜ)`;
- `InjOn Φ (MandelbrotSetᶜ)`;
- `MapsTo Φ (MandelbrotSetᶜ) {w : ℂ | 1 < ‖w‖}`;
- surjectivity onto `{w : ℂ | 1 < ‖w‖}`;
- normalization
  ```lean
  Tendsto (fun c : ℂ => Φ c / c) (comap (fun z : ℂ => ‖z‖) atTop) (𝓝 1).
  ```

Classically this is the parameter Böttcher map `Φ(c) = φ_c(c)` on the exterior of `M`.

### B. Exterior conformal equivalence

Package the same content as a biholomorphic equivalence between

```lean
MandelbrotSetᶜ
```

and

```lean
{w : ℂ | 1 < ‖w‖}.
```

This is better conceptually, but current library support does not yet provide a ready-made bundled conformal-equivalence abstraction for this route.

### C. Spherical / one-point-compactified version

State the theorem on `ℂ∞`/sphere language: the component of `∞` in the complement of `M` is conformally equivalent to the exterior disk, with normalization at `∞`.

This is mathematically cleanest, but further from the current repo APIs than (A).

## Audit conclusions from current code

### 1. `ParameterEscapeExhaustion.lean` gives connectedness of the exterior, not uniformization

The checked route now proves

```lean
mandelbrotSet_compl_isConnected
```

by escape-level exhaustion. This is real progress, but it only supplies the **fullness/exterior-connectedness** side. It does **not** by itself produce:

- a holomorphic exterior coordinate;
- monodromy-free continuation of that coordinate;
- injectivity/surjectivity onto the exterior disk;
- or any ordinary-plane simple-connectedness theorem.

So finite escape exhaustion helps only at the level “the complement is connected/full”, not at the actual parameter-uniformization step.

### 2. The repo already has genuine near-infinity parameter Böttcher infrastructure

From the current Böttcher files, the abstraction frontier is no longer the main problem.

Already present in checked source:

- `logSeriesNearInfinityParameterFamily` in `BottcherParamHolo.lean`;
- `exists_param_holo_bottcher_inverse` in `BottcherParamInverse.lean`;
- theorem-facing packages in `BottcherMotion.lean`, including
  - `GenuineBottcherLocalParameterFamilyData`,
  - `GenuineBottcherNearInfinityParameterFamilyData`,
  - `GenuineBottcherNearInfinityParameterExtensionData`.

So the repo already knows how to talk about a **genuine** parameter Böttcher family near infinity and its local inverse dependence on the parameter.

### 3. The outside-plan file is still mostly roadmap/scaffolding for the parameter route

`BottcherOutsidePlan.lean` contains useful strategic scaffolding, but not a finished theorem giving the global parameter coordinate on `MandelbrotSetᶜ`.

In particular, the historical proxy route is not the correct endpoint: the sound route is through the genuine Böttcher family, not placeholder/proxy coordinates.

### 4. The smallest honest next theorem is not a generic Riemann-map theorem

After the exterior-connectedness theorem, the smallest genuine next source theorem is:

> a nontrivial theorem that upgrades the existing **near-infinity parameter Böttcher family** to a parameter coordinate on an open exterior neighborhood and packages its local inverse/continuation data in theorem-facing form.

Concretely, the next theorem should stay **inside the existing Böttcher API** rather than detouring through a generic exterior simple-connectedness / Riemann mapping theorem.

## Smallest genuine non-axiomatic next theorem

The best next target is:

### Near-infinity parameter coordinate packaging theorem

A theorem/constructor of the shape:

```lean
∃ h : GenuineBottcherNearInfinityParameterExtensionData c₀, True
```

for a concrete near-infinity center `c₀` (or directly a global outside-`M` package if already naturally expressible).

More explicitly: extend the checked near-infinity family plus parametrized inverse into a theorem-facing package that states:

- joint parameter/fiber holomorphy on a genuine outside neighborhood;
- conjugacy to squaring on that neighborhood;
- normalized behavior at infinity;
- local inverse branches depending holomorphically on the parameter.

This is smaller and more honest than jumping directly to global surjectivity onto `{‖w‖>1}`.

## Why this is the right next brick

Because the remaining difficulty is **continuation and global assembly**, not basic local analyticity.

The checked ingredients already cover:

- near-infinity parameter holomorphy;
- local inverse holomorphy in the parameter;
- the theorem-facing data structures meant to express exactly this route.

What is still missing is the global step that turns those local pieces into the actual parameter exterior coordinate `Φ(c)=φ_c(c)` across all of `MandelbrotSetᶜ`.

That global step requires some combination of:

- continuation along the connected escape locus;
- compatibility/uniqueness of local branches;
- monodromy triviality / branch coherence;
- and finally global image/injectivity/surjectivity conclusions.

Those are much closer to the current formal frontier than a fresh generic planar-uniformization development.

## Does finite escape exhaustion help?

Yes, but only partially.

What it genuinely supplies:

- `MandelbrotSetᶜ` is connected;
- escape loci admit manageable finite-level exhaustions;
- this gives the right topological base for continuation/uniqueness arguments on the exterior.

What it does **not** yet supply:

- simply connectedness in ordinary `ℂ`;
- no-loop/monodromy triviality for analytic continuation of branches;
- a direct global inverse theorem for the parameter coordinate.

So the current finite escape exhaustion can support the **domain connectedness** part of a continuation argument, but it does not by itself close the continuation/monodromy seam.

## Corrected roadmap after Prompt 88

1. **Stop** pursuing ordinary `IsSimplyConnected (MandelbrotSetᶜ)` as the next target.
2. Reuse the checked theorem `mandelbrotSet_compl_isConnected` only as exterior connectedness/fullness input.
3. Continue in the existing Böttcher-family framework:
   - package the genuine near-infinity family + parametrized inverse cleanly;
   - formulate the smallest continuation theorem on the exterior;
   - only then target the full parameter Böttcher map `Φ(c)=φ_c(c)`.
4. Treat global surjectivity/uniformization as a later consequence of the parameter Böttcher theory, not as the next isolated theorem.

## Honest blocker statement

The current blocker is **not** “prove ordinary simple connectedness of `MandelbrotSetᶜ`.”

The real blocker is:

> build a genuine global parameter Böttcher coordinate from the existing near-infinity family by continuation/coherence on the connected escape locus, and theoremize the required injectivity/image/normalization package.

That is the correct frontier after Result 85.

## Files audited

- `Mlc/ParameterEscapeExhaustion.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherParamInverse.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherMotion.lean`
- `Mlc/Quadratic/Complex/Bottcher/BottcherOutsidePlan.lean`
- `Mlc/Quadratic/Complex/Bottcher/GreenFunctionRayInversion.lean`
- prior result/task files for Prompts 76–78

## No code changes

Per prompt instructions, I did not edit Lean source. This result records the corrected target and the smallest honest next theorem direction.