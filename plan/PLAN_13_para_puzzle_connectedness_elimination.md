# PLAN 13: Eliminate `Quadratic.para_puzzle_piece_inter_mandelbrot_connected`

**Status:** NEW  
**Difficulty:** High  
**Goal:** Remove the newly exposed finite-branch / para-puzzle connectedness axiom
from the root frontier.

---

## Why this matters now

The recent true-modulus cutover exposed a previously hidden root dependency:

```lean
MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected
```

This is now part of the checked project frontier, so the repository cannot reach
the “only built-in axioms left” milestone without eliminating it.

---

## Current Role in the Graph

This axiom sits on the finite-branch / para-puzzle side of the proof rather than
the infinitely-renormalizable primitive route.

So it should be treated as a **separate elimination project**, not mixed into the
primitive Feigenbaum theoremization work.

---

## Concrete Work Plan

### Phase A. Locate every dependency

Files to inspect:

- `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
- `Mlc/Quadratic/Complex/ParaPuzzle*.lean`
- `Mlc/MainConjecture.lean`

Deliverable:

- one exact dependency chain from
  `para_puzzle_piece_inter_mandelbrot_connected`
  to `mlc_conjecture`.

### Phase B. Replace the axiom by theorem surfaces

If the current statement is too strong, split it into smaller lemmas:

1. nonempty / closed / nested para-puzzle pieces,
2. connectedness of each relevant piece,
3. connectedness of the intersection with Mandelbrot,
4. final finite-branch local-connectivity application.

### Phase C. Prove the split lemmas from existing para-puzzle machinery

Prefer:

- direct topological arguments already available in the repo,
- existing Yoccoz / para-puzzle infrastructure,
- theoremizing local helper lemmas instead of preserving one large axiom.

---

## Success Criterion

`MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` disappears from
`check_axioms`, leaving only the genuinely infinite-branch frontier.

