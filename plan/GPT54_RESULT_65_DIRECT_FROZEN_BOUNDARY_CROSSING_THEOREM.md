# GPT-5.4 Result 65 — Direct frozen boundary-crossing theorem

## Prompt executed

`@plan/GPT54_PROMPT_65_DIRECT_FROZEN_BOUNDARY_CROSSING_THEOREM.md`

## Outcome

Honest hard stop. I did **not** make Lean source edits, because the repository still
lacks the substantive classical boundary theorem needed to prove the frozen-straddling
connectedness target directly.

The target remains:

```lean
IsConnected
  ({c' | green_function c (c' - c) < (1 / 2 : ℝ)^n} ∩ MandelbrotSet)
```

under `c ∈ MandelbrotSet` and the straddling hypothesis.

## What Stage 3 was supposed to add

Stages 1–2 already established that elementary set geometry is not enough, and that a
component-attachment theorem for the exact frozen intersection is missing.

Stage 3 asked whether that missing property itself could now be proved directly from the
currently checked geometry of:

- `green_function c`;
- the frozen Green translate `S c n`;
- `MandelbrotSet`;
- component/frontier/closure facts already in the repo.

The audit answer is: **no**.

## Exact frozen set under study

As before, let

```lean
S c n := {c' : ℂ | green_function c (c' - c) < (1 / 2 : ℝ)^n}.
```

Already checked facts still available:

- `S c n` is open;
- `S c n` is connected;
- `S c n` is bounded;
- if `c ∈ MandelbrotSet`, then `c ∈ S c n`;
- straddling means `∃ x ∈ S c n, x ∉ MandelbrotSet`;
- in the straddling case, `¬ IsOpen (S c n ∩ MandelbrotSet)`.

These are all true and useful, but still insufficient to prove the target.

## What I searched for and did not find

I explicitly checked for any theorem in the repository that would support a genuine
frozen boundary-crossing argument, including results about:

- closures of components meeting a common boundary set;
- frontier/contact theorems for separated subsets of a connected open region;
- prime-end or Carathéodory theory;
- Jordan/crosscut/wake structure;
- external-ray landing results applicable to the exact frozen translate;
- continuum/full continuum or connected-complement structure for the target sets.

What I found:

- `GreenSublevelConnectedDirect.lean` contains a **dynamical** component-attachment proof
  for `GreenSublevel c n`, using harmonicity in the basin and a frontier minimum
  principle.
- `BasinConnected.lean` contains strong no-separation arguments for certain **open basin
  superlevel** sets, driven by max-modulus/frontier estimates.
- `ParaPuzzleCarvingReduction.lean` proves only a **negative** frontier fact:
  the straddling target is not open, blocking the carving-by-motion reduction.

What I did **not** find is any theorem that transfers these methods to the exact set
`S c n ∩ MandelbrotSet`.

## Why the direct frozen proof still cannot go through

### 1. No analytic function is available on the exact target

The successful direct proofs elsewhere in the repo use analytic/harmonic structure on an
open set and compare interior values to boundary/frontier values.

But the frozen intersection

```lean
S c n ∩ MandelbrotSet
```

is not open in the straddling case, and the repository does not furnish a harmonic or
holomorphic object on this exact set whose boundary behavior would force no separation.

So the max-modulus / minimum-principle argument does not transplant.

### 2. No proved boundary-contact theorem exists for components of the target

A direct proof would need something like:

> every connected component of `S c n ∩ MandelbrotSet` has closure meeting a common
> connected subset of `S c n ∩ ∂MandelbrotSet` or `∂S c n ∩ MandelbrotSet`.

This is exactly the sort of theorem Stage 2 isolated. It is still absent.

### 3. No proved external-access/landing structure connects interior and exterior sides

A plausible classical route would use some control of how the complement of
`MandelbrotSet` crosses `S c n` — e.g. through landing rays, wakes, crosscuts, or prime
ends — to show that two putative Mandelbrot components inside `S c n` cannot remain
separate.

The repository does not currently prove any such structure for the frozen formulation.

## Exact missing classical theorem

The first missing ingredient can now be stated more sharply.

A sufficient missing theorem would be a result of one of the following exact forms.

### Form A — boundary-crossing uniqueness

For `c ∈ MandelbrotSet`, if `S c n` straddles `∂MandelbrotSet`, then every connected
component of `S c n ∩ MandelbrotSet` has closure meeting a **common connected subset** of
`S c n ∩ ∂MandelbrotSet`; consequently the intersection has only one component.

### Form B — no-separation through the frozen boundary

If `U` and `V` are a separation of `S c n ∩ MandelbrotSet`, then the closures of `U` and
`V` in `S c n` must meet a boundary set whose already-proved connectedness forces the two
sides to merge.

### Form C — frozen crosscut/continuum theorem

The pair `(S c n, S c n ∩ MandelbrotSet)` satisfies a specialized continuum or crosscut
property ensuring that a connected open bounded ambient set with a single Mandelbrot
boundary-contact regime cannot contain two disjoint Mandelbrot components.

Any one of these would be enough in spirit. None is currently derivable from the checked
facts already in the repo.

## Is this theorem known for the frozen formulation?

Not in the current repository.

More importantly, the surrounding proof literature is typically expressed not for this
raw frozen Green translate alone, but for **genuine para-puzzle / moving-boundary
constructions** with parameter↔dynamical correspondence and controlled boundary motion.
That is exactly the machinery Stages 61–62 found to be missing on the source side.

So even mathematically, the frozen boundary-crossing theorem appears to be asking for a
classical conclusion that is usually obtained *through* the parapuzzle correspondence,
not from the frozen Green-translate geometry by itself.

## Why I made no Lean edits

Any Lean edit at this point would have been cosmetic only:

- wrappers for closure/frontier facts;
- repackaging straddling witnesses;
- renaming the missing theorem into a new definition.

None of that would constitute a genuine proof of the Stage-3 objective, and the prompt
explicitly forbids encoding the missing theorem as an axiom or equivalent wrapper.

So the correct action was to stop and report the exact missing theorem.

## Final verdict

Prompt 65 does **not** produce a direct frozen boundary-crossing theorem.

The honest conclusion is:

- the repository does not yet contain a valid direct proof that the frozen straddling
  intersection `S c n ∩ MandelbrotSet` is connected;
- the missing ingredient is a genuine classical **boundary-crossing / crosscut /
  component-closure theorem** for the exact frozen formulation;
- current checked mathematics supports that this theorem is **not derivable** from the
  existing elementary, harmonic, or basin-side lemmas alone.

So Stage 3 ends in a precise blocker report, not a Lean theorem.