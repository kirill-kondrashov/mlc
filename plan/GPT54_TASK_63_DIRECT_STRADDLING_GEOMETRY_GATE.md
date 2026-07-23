# TASK 63 — Direct straddling geometry gate

## Goal

Start a direct proof of:

```lean
green_sublevel_translate_inter_mandelbrot_connected_straddling
```

without using any frontier or equivalent connectivity axiom.

## Required set normalization

Use:

```lean
S c n := {c' : ℂ | green_function c (c' - c) < (1 / 2 : ℝ)^n}
```

Establish elementary facts about `S c n` from existing theorems:

- `S c n` is open;
- `S c n` is connected and bounded;
- translation to `GreenSublevel c n`;
- `c ∈ S c n` when `c ∈ MandelbrotSet`;
- the exact content of
  `¬ S c n ⊆ MandelbrotSet`.

Search for valid stronger properties such as fullness, path connectedness, or
controlled boundary components, but prove them rather than assume them.

## Proof gate

Determine whether the existing facts yield a valid direct reduction for
`S c n ∩ MandelbrotSet`. Explicitly reject the false inference that two
connected sets have connected intersection.

If a required separation/boundary lemma is missing, stop and report it. Do not
invent a theorem merely to match the target.

## Constraints

- no frontier axiom;
- no old para-puzzle connectivity axiom;
- no moving-window provider;
- no new axiom, `sorry`, or `admit`;
- no Böttcher continuation work;
- preserve the root theorem and old APIs;
- do not commit.

Write the result to:

`plan/GPT54_RESULT_63_DIRECT_STRADDLING_GEOMETRY_GATE.md`
