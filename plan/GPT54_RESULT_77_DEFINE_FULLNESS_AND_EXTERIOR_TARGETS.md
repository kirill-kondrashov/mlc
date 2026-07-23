# GPT-5.4 Result 77 — Define Fullness and Exterior Targets

## Outcome

Prompt 77 is completed as a **specification/source artifact**.

I did **not** add Lean source, new axioms, `sorry`, or placeholder providers.
The honest result is a precise target specification for the parameter-exterior route, plus the classical source statements that would be needed to make Prompt 76 implementable.

## API audit summary

### What should be reused from the current repository / Mathlib

From `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean` we already have the right base facts:

- `isOpen_compl_mandelbrotSet : IsOpen (MandelbrotSetᶜ)`
- `isClosed_mandelbrotSet : IsClosed MandelbrotSet`
- `isCompact_mandelbrotSet : IsCompact MandelbrotSet`
- `mandelbrotSet_subset_closedBall_two : MandelbrotSet ⊆ Metric.closedBall (0 : ℂ) 2`

From `Mlc/Quadratic/Complex/Axioms.lean` we already have:

- `mandelbrot_set_connected : IsConnected MandelbrotSet`

From Mathlib, the reusable simple-connectedness predicate is:

- `IsSimplyConnected` / `SimplyConnectedSpace`
  in `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`

These should be reused rather than replaced.

### What is not already formalized

The repo does **not** currently define or prove any of the following:

- a project notion of **full** compact planar set;
- a bundled theorem identifying compact connected planar sets as a continuum notion to reuse;
- connectedness / path connectedness / simple connectedness of `MandelbrotSetᶜ`;
- a bridge theorem of the form “full compact subset of `ℂ` ⇒ simply connected complement”;
- a usable exterior-domain uniformization theorem for an unbounded simply connected domain in `ℂ`.

Mathlib appears to have the **predicate** `IsSimplyConnected`, but not the complex-analytic Riemann/exterior uniformization theorem needed for the parameter coordinate.

## Recommended Lean target formulations

The correct route is to keep the targets minimal and non-duplicative.

### 1. Fullness target

Because no existing project definition appears to exist, the smallest justified project-local definition would be:

```lean
/-- A compact planar set is full if its complement is connected. -/
def IsFull (K : Set ℂ) : Prop := IsConnected (Kᶜ)
```

This is the recommended notion for the parameter-exterior plan because it matches the classical planar usage needed here. It should **not** be introduced unless/until the project is ready to prove lemmas with it; for Prompt 77 it is enough to specify it.

With that definition, the intended target would be:

```lean
theorem mandelbrotSet_isFull : IsFull MandelbrotSet
```

### 2. Compact connected continuum package

There is no need for a new `Continuum` structure. The repository already has the constituents needed for the classical continuum package:

```lean
IsCompact MandelbrotSet
IsConnected MandelbrotSet
```

So the “Mandelbrot set is a full compact continuum” target should be represented by the three separate theorems:

```lean
theorem isCompact_mandelbrotSet : IsCompact MandelbrotSet
theorem mandelbrot_set_connected : IsConnected MandelbrotSet
theorem mandelbrotSet_isFull : IsFull MandelbrotSet
```

The first two already exist; only the fullness theorem is missing.

### 3. Complement connectedness / simple connectedness target

The intended exterior-domain target should reuse Mathlib’s existing predicate:

```lean
theorem mandelbrotSet_compl_isSimplyConnected :
  IsSimplyConnected (MandelbrotSetᶜ)
```

Since `isOpen_compl_mandelbrotSet` is already available, this is the right topological theorem to aim for. If later proofs need a weaker intermediate theorem, the natural stepping stone is:

```lean
theorem mandelbrotSet_compl_isConnected : IsConnected (MandelbrotSetᶜ)
```

but the actual parameter-uniformization route needs the stronger simple-connectedness package.

### 4. Exterior-domain normalization target

The prompt specifically asked for the unbounded-domain normalization needed for an exterior coordinate. The correct mathematical target is **not** merely “some biholomorphism to the unit disk”; it is a conformal coordinate on the exterior, normalized at infinity.

At specification level, the desired shape is:

```lean
/-- There exists a holomorphic coordinate on the Mandelbrot exterior,
normalized by `Φ(z) / z → 1` at infinity. -/
theorem exists_mandelbrot_exterior_coordinate :
  ∃ Φ : ℂ → ℂ,
    DifferentiableOn ℂ Φ (MandelbrotSetᶜ) ∧
    InjOn Φ (MandelbrotSetᶜ) ∧
    MapsTo Φ (MandelbrotSetᶜ) {w : ℂ | 1 < ‖w‖} ∧
    Tendsto (fun z : ℂ => Φ z / z) (comap (fun z : ℂ => ‖z‖) atTop) (𝓝 1)
```

This is only a **target shape**, not an implementation recommendation. In practice a more structured statement (e.g. with an equivalence/homeomorphism/conformal equivalence record) may be preferable once the library support exists.

The key point is that the normalization must be explicitly **at infinity**, and the current repo already uses the filter

```lean
comap (fun z : ℂ => ‖z‖) atTop
```

for such statements, so that is the normalization/filter convention worth reusing.

## Recommended dependency order

The clean formal dependency order is:

1. `mandelbrotSet_isFull`
2. `mandelbrotSet_compl_isSimplyConnected`
3. exterior uniformization / normalized coordinate theorem
4. parameter external arcs / boundary parametrization

Prompt 76 was blocked because stages (2) and (3) are both missing.

## Classical source statements to attach to this route

### Source target 1 — fullness of the Mandelbrot set

Use the classical Douady–Hubbard theorem that the Mandelbrot set is connected, together with the standard planar fact that a connected compact subset of `ℂ` is full iff its complement is connected. For the project’s source ledger, the direct mathematical target to cite is:

- **Douady–Hubbard,** *Étude dynamique des polynômes complexes* (Orsay notes, 1984/85), Chapter VIII, Theorem 1: the Mandelbrot set is connected.

This source already supports the in-repo axiom `mandelbrot_set_connected`. It does **not by itself** give the Lean fullness theorem unless the project separately formalizes the planar complement theorem.

### Source target 2 — full compact continuum ⇒ simply connected complement

The classical planar topology statement needed is:

- If `K ⊂ ℂ` is compact and full (equivalently, `ℂ \ K` is connected), then `ℂ \ K` is simply connected.

A standard reference class for this statement is elementary complex analysis / plane topology texts treating simply connected planar domains via complement components. Suitable classical sources include:

- **Pommerenke,** *Boundary Behaviour of Conformal Maps* — standard planar domain background;
- **Conway,** *Functions of One Complex Variable I* — simple connectedness / Riemann mapping background;
- **Ransford,** *Potential Theory in the Complex Plane* — planar complement and Green-function background.

For the plan, the important point is the exact theorem shape above; the repo currently lacks its formalization.

### Source target 3 — unbounded exterior uniformization theorem

The needed analytic theorem is the exterior-version Riemann mapping statement:

- If `Ω ⊂ ℂ` is a proper simply connected unbounded domain containing `∞` in the sphere picture, then there exists a conformal isomorphism
  `Φ : Ω → {w : ℂ | 1 < ‖w‖}`
  normalized by `Φ(z)/z → a` as `z → ∞`, with the usual normalization choosing `a > 0` and in particular `a = 1` after rescaling.

Standard sources for this are classical Riemann mapping / exterior mapping treatments, for example:

- **Pommerenke,** *Boundary Behaviour of Conformal Maps*;
- **Conway,** *Functions of One Complex Variable I*;
- **Ahlfors,** *Complex Analysis*.

This is exactly the theorem family missing from bundled Mathlib for the Prompt 76/77 route.

## Honest conclusions for the plan

1. Prompt 77 should remain a **specification/source** step, not a source-code implementation step.
2. The right simple-connectedness notion to reuse is `IsSimplyConnected`; no competing project predicate is needed there.
3. A small project-local `IsFull` definition would be reasonable **only when** the repo is ready to prove/use it; it is not justified as a standalone code change here.
4. The actual blocker chain remains unchanged:
   - missing planar theorem from fullness to simply connected exterior;
   - missing exterior uniformization theorem in Mathlib / repo.

## Files audited

- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/Axioms.lean`
- `Mlc/Quadratic/Complex/Bottcher/ChordalMetric.lean`
- `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean`
- broad Mathlib searches for complement/simple-connectedness/unbounded-domain APIs

## No source edits

Per prompt instructions, I did not edit Lean source. This result only records the exact targets and sources that the parameter-exterior route would need.