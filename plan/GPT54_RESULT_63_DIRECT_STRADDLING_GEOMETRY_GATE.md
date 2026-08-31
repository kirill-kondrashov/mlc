# GPT-5.4 Result 63 — Direct straddling geometry gate

## Prompt executed

`@plan/GPT54_PROMPT_63_DIRECT_STRADDLING_GEOMETRY_GATE.md`

## Outcome

Honest hard stop. I did **not** modify Lean source, because the elementary direct
geometry already available in the repository is not enough to prove

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
```

without introducing a genuinely new boundary/separation theorem.

## Normalized frozen set

I worked with

```lean
S c n := {c' : ℂ | green_function c (c' - c) < (1 / 2 : ℝ)^n}
```

This is exactly the set already used in `ParaPuzzleConnectivity.lean`.

## Elementary facts already available from checked code

These are all already present, directly or by immediate normalization.

### 1. Openness of `S c n`

Already available in substance:
- `GreenSublevelConnectedDirect.isOpen_greenSublevel`
- the translated form is reproved privately in
  `ParaPuzzleCarvingReduction.greenSublevel_translate_isOpen`.

Reason: `S c n` is the strict sublevel of the continuous map
`c' ↦ green_function c (c' - c)`.

### 2. Translation equivalence with `GreenSublevel c n`

Already encoded in the proof of
`green_sublevel_translate_connected` in `ParaPuzzleConnectivity.lean`:

```lean
(fun w => w + c) '' GreenSublevel c n = S c n
```

So `S c n` is literally the translate by `+c` of the dynamical Green sublevel.

### 3. Connectedness of `S c n`

Already proved theorem-level:

```lean
green_sublevel_translate_connected
```

The proof transports the direct connectedness theorem
`green_sublevel_connected_direct` for `GreenSublevel c n` through translation.

### 4. Boundedness of `S c n`

Available from `bounded_sublevel_green_function` in
`Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`, together with translation.

At the dynamical level,

```lean
{w | green_function c w < (1/2)^n}
```

is bounded. Therefore `S c n = (fun w => w + c) '' GreenSublevel c n` is bounded as
an isometric image under translation.

This boundedness fact appears to be available but is not yet packaged under the
specific name `bounded_green_sublevel_translate`; such a wrapper would be a
legitimate small future lemma if needed.

### 5. Basepoint membership / nonemptiness

For `c ∈ MandelbrotSet`, the set `S c n` contains `c`.

Reason:
- `0 ∈ GreenSublevel c n` is already proved as
  `Quadratic.green_sublevel_contains_0 c n hc`;
- under the translation `w ↦ w + c`, this becomes `c ∈ S c n`.

So the straddling target `S c n ∩ MandelbrotSet` is nonempty whenever `c ∈ M`,
because it contains `c`.

### 6. Exact meaning of the straddling hypothesis

The current frontier axiom is restricted to:

```lean
hstraddle : ¬ (S c n ⊆ MandelbrotSet)
```

By `not_subset`, this means exactly:

```lean
∃ x, x ∈ S c n ∧ x ∉ MandelbrotSet
```

So the straddling case is precisely: the connected open bounded translate `S c n`
contains at least one exterior point, while also containing the Mandelbrot point
`c`.

### 7. Valid openness / non-openness facts about the target intersection

This part is already proved in `ParaPuzzleCarvingReduction.lean`.

- `S c n` is open.
- `MandelbrotSetᶜ` is open.
- In the straddling case,

```lean
¬ IsOpen (S c n ∩ MandelbrotSet)
```

This is the key no-go fact used to refute the carving-by-motion route.

## Existing direct reductions checked during the audit

### A. Trivial nested strata are already discharged

`ParaPuzzleConnectivity.lean` already proves:

- `green_sublevel_translate_inter_mandelbrot_connected_of_subset`
- `green_sublevel_translate_inter_mandelbrot_connected_of_superset`

So the only live frontier is the genuine intermediate/straddling case.

### B. The motion-carving reduction fails on the live frontier

`ParaPuzzleCarvingReduction.lean` proves:

- `isConnected_greenSublevel_inter_mandelbrot_of_carvedByMotion`
- `not_paraPieceCarvedByMotion_of_straddling`

Hence the attempted reduction

```lean
S c n ∩ MandelbrotSet = H.f t '' S c n
```

cannot hold in the straddling case, because the left-hand side is not open while
such a slice image is open.

### C. The invalid intersection principle is explicitly unavailable

There is no valid route from
- `IsConnected (S c n)` and
- `IsConnected MandelbrotSet`

to
- `IsConnected (S c n ∩ MandelbrotSet)`.

This is false in general, and the repository contains no specialized theorem that
would make it true here.

## First missing geometric lemma

After the audit, the first genuinely missing ingredient is **not** another
transport/motion lemma. It is a specialized direct geometric theorem controlling how
`∂MandelbrotSet` can meet the connected open bounded translate `S c n`.

A representative missing statement would have the following shape:

> If `c ∈ MandelbrotSet` and `S c n` straddles `∂MandelbrotSet`, then every connected
> component of `S c n ∩ MandelbrotSet` accumulates on a distinguished/common boundary
> portion of `S c n`, forcing uniqueness of the component containing `c`.

Equivalently, one needs a **boundary-crossing / component-attachment theorem** for the
frozen set `S c n` relative to `MandelbrotSet`.

Nothing currently checked in the repository supplies:
- fullness of `S c n ∩ MandelbrotSet`;
- path connectedness of `S c n` together with a usable component-crossing theorem;
- local connectedness or prime-end control of `∂MandelbrotSet ∩ S c n`;
- uniqueness of an attached Mandelbrot component inside `S c n`;
- any replacement bridge from Green-sublevel geometry alone to parameter-piece
  connectedness.

## Why I did not make Lean edits

The prompt allowed small focused lemmas, but the elementary layer is already present:
open / connected / translated / nonempty / bounded / straddling-witness / not-open are
all either explicit or immediate from existing checked proofs.

Adding wrappers without closing the actual geometric gap would not honestly advance the
frontier theorem. So I made no speculative Lean changes.

## Final verdict

Prompt 63 isolates the frontier correctly but does **not** discharge it.

The honest conclusion is:

- the direct elementary geometry of `S c n` is already essentially exhausted;
- the carving/motion route is formally refuted on the straddling stratum;
- the first missing ingredient is a new **direct component-attachment / boundary-crossing
  theorem** for `S c n ∩ MandelbrotSet`.

That missing theorem is exactly the right subject for the next lead prompt.