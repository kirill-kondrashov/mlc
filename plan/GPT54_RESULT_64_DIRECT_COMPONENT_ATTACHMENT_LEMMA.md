# GPT-5.4 Result 64 — Direct component attachment lemma

## Prompt executed

`@plan/GPT54_PROMPT_64_DIRECT_COMPONENT_ATTACHMENT_LEMMA.md`

## Outcome

Honest hard stop again. I did **not** make Lean source edits, because the current
repository does not contain enough checked geometry to prove a substantive
component-attachment or no-separation theorem for

```lean
S c n ∩ MandelbrotSet,
```

where

```lean
S c n := {c' : ℂ | green_function c (c' - c) < (1 / 2 : ℝ)^n}.
```

## What I checked

I audited the exact Stage-2 target against the currently proved material in:

- `Mlc/ParaPuzzleConnectivity.lean`
- `Mlc/ParaPuzzleCarvingReduction.lean`
- `Mlc/GreenSublevelConnectedDirect.lean`
- `Mlc/BasinConnected.lean`
- `Mlc/ParaPuzzleContainment.lean`
- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/MandelbrotEquivalence.lean`

## Confirmed usable facts

From Stage 1 and existing checked code, the following remain valid and relevant:

1. `S c n` is open.
2. `S c n` is connected.
3. `S c n` is bounded.
4. If `c ∈ MandelbrotSet`, then `c ∈ S c n`, hence
   `(S c n ∩ MandelbrotSet).Nonempty`.
5. In the straddling case, `∃ x ∈ S c n, x ∉ MandelbrotSet`.
6. In the straddling case,

   ```lean
   ¬ IsOpen (S c n ∩ MandelbrotSet).
   ```

These facts are enough to rule out the motion-carving reduction, but not enough to
force connectedness of the intersection.

## What potentially relevant component technology actually exists

### A. Green-sublevel component attachment exists only on the dynamical side

`GreenSublevelConnectedDirect.lean` proves the key lemma

```lean
connectedComponentIn_greenSublevel_inter_K_nonempty
```

showing that every connected component of `GreenSublevel c n` meets `K c`.
This is exactly the kind of attachment theorem one would like for the parameter
intersection, but it only applies to the **unintersected dynamical Green sublevel**.

Its proof uses facts unavailable for the parameter intersection target:

- the complement is the basin of infinity, where the Green function is harmonic;
- a frontier minimum-principle contradiction on a connected component disjoint from `K c`.

There is no corresponding harmonic function / max-min argument in the repository for
components of `S c n ∩ MandelbrotSet`.

### B. Basin separation lemmas do not transfer to `S ∩ M`

`BasinConnected.lean` has strong no-separation tools for superlevel/exterior sets,
notably:

- `frontier_side_subset_compl`
- `maxmod_absurd`
- `isPreconnected_orbit_superlevel`

But these arguments are built around holomorphic/max-modulus behavior of orbit maps on
open sets. The target `S c n ∩ MandelbrotSet` is not open in the straddling case, and
no analogous analytic function is available whose boundary values would contradict a
separation of that exact set.

So these are useful as analogies, not as transferable lemmas.

### C. No exact local-connectedness/fullness theorem is available for the target

I also checked whether the repository already proves any of the following in a form that
would apply here:

- local connectedness of `MandelbrotSet`;
- fullness / connected complement of `MandelbrotSet` or of `S c n ∩ MandelbrotSet`;
- simply connectedness or prime-end control of the complement;
- a theorem that every component of `S ∩ MandelbrotSet` meets a common connected core.

Nothing like this is available as a checked theorem for the exact sets in the prompt.

`Mlc/MandelbrotEquivalence.lean` only states equivalence-of-formulations for MLC; it
does **not** provide local connectedness of `MandelbrotSet`.

## Why the obvious attachment ideas fail

### 1. “Every component meets `c`” is not currently derivable

We do know `c ∈ S c n ∩ MandelbrotSet`, but there is no proved theorem forcing every
connected component of the intersection to meet the component containing `c`.
That would already amount to the desired connectedness.

### 2. “Every component meets a common core” has no proved core

A natural candidate would be some distinguished connected subset of `MandelbrotSet`
contained in `S c n`, analogous to `K c` on the dynamical side. But the repository only
provides:

- `c ∈ MandelbrotSet`, and
- in other contexts, that all Mandelbrot parameters lie in para-puzzle pieces.

It does **not** provide any nontrivial connected core `C ⊆ S c n ∩ MandelbrotSet` such
that every component of the intersection is known to meet `C`.

### 3. “A separation contradicts a frontier property” lacks the frontier theorem

Stage 2 explicitly asked whether a separation of `S c n ∩ MandelbrotSet` could contradict
some already proved boundary/frontier property. The audit says: not yet.

We do have the negative frontier fact

```lean
¬ IsOpen (S c n ∩ MandelbrotSet)
```

but that only blocks the carving-by-motion image argument. It does **not** imply that a
separation is impossible.

To turn separation into contradiction, one would need a theorem of the form:

- every frontier piece of a separated side lies in a common connected boundary set, or
- each component closure must meet a distinguished boundary continuum, or
- crossing from the Mandelbrot point `c` to an exterior point in `S` forces a boundary
  contact that merges all intersection components.

No such theorem is currently checked.

## First missing mathematical property

The first missing ingredient is more precise now than in Stage 1:

> A **parameter-side component-attachment / boundary-crossing theorem** for the exact set
> `S c n ∩ MandelbrotSet`, showing that every connected component of this intersection has
> closure meeting a common connected subset (or common boundary continuum) inside `S c n`.

Equivalent usable forms would include any one of the following:

1. **Common-core attachment:**
   every connected component of `S c n ∩ MandelbrotSet` meets a connected subset
   `C ⊆ S c n ∩ MandelbrotSet`.

2. **Boundary-contact uniqueness:**
   every connected component closure of `S c n ∩ MandelbrotSet` meets a common connected
   subset of `∂S c n ∩ MandelbrotSet` or of `S c n ∩ ∂MandelbrotSet`.

3. **No-separation theorem for the exact frozen intersection:**
   any decomposition of `S c n ∩ MandelbrotSet` into disjoint separated nonempty relatively
   open pieces contradicts a proved boundary property specific to `S c n` and `MandelbrotSet`.

At present, none of these forms is available from checked repository facts alone.

## Why no Lean edit was honest

There is room for tiny wrapper lemmas, but they would only rename facts already known:

- openness/connectedness/boundedness of `S c n`;
- nonemptiness of `S c n ∩ MandelbrotSet`;
- witness form of the straddling hypothesis.

Those wrappers do not advance the actual Stage-2 obstacle, which is a new attachment or
boundary-crossing argument. So I made no source changes.

## Final verdict

Prompt 64 does not yet yield a proved direct component-attachment lemma.

What it *does* accomplish is sharpening the blocker:

- Stage 1 isolated the need for a direct boundary/component theorem.
- Stage 2 shows that the presently available component machinery lives only on the
  dynamical/basin side and does not transfer to the exact parameter intersection.

So the next honest frontier is a theorem specifically about **component closures and
boundary contact for `S c n ∩ MandelbrotSet`**.