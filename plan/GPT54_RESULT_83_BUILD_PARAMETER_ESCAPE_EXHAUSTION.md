# GPT-5.4 Result 83 — Build Parameter Escape Exhaustion

## Outcome

Prompt 83 is currently **blocked at the requested finite-level monotonicity package**.

I audited the actual orbit/escape lemmas in the repository and attempted a direct source implementation, but the crucial monotonicity step

```lean
ParameterEscapeLevel n ⊆ ParameterEscapeLevel (n + 1)
```

for

```lean
def ParameterEscapeLevel (n : ℕ) : Set ℂ :=
  {c : ℂ | 2 < ‖orbit c 0 (n + 1)‖}
```

does **not** follow from the currently available elementary lemmas in a clean checked way.

## What does work from the current repo

The following pieces are already genuinely available or straightforward from existing proofs:

1. continuity of `c ↦ orbit c 0 (n + 1)` via
   - `continuous_orbit_zero_param`;
2. openness of each finite level
   ```lean
   IsOpen {c : ℂ | 2 < ‖orbit c 0 (n + 1)‖};
   ```
3. the forward implication
   ```lean
   2 < ‖orbit c 0 (n + 1)‖ → c ∉ MandelbrotSet
   ```
   by combining `R_ge_two` with `not_mandelbrot_of_orbit_gt_R`;
4. the exhaustion direction
   ```lean
   c ∉ MandelbrotSet → ∃ n, 2 < ‖orbit c 0 (n + 1)‖
   ```
   using the same unbounded-orbit argument already used in `isOpen_compl_mandelbrotSet`.

So the union identity is plausibly within reach **once** the formal finite-level package is chosen carefully.

## Exact blocker

The existing monotonic growth lemma surface is centered on thresholds of the form

```lean
R c < ‖orbit c z n‖
```

and on starting points already outside the escape radius. For example, the available monotonicity lemmas use:

- `escape_lemma`
- `norm_orbit_ge_of_norm_ge_R`

but these require a hypothesis already above `R c`, not just above the constant `2`.

For parameters with `R c > 2`, the statement

```lean
2 < ‖orbit c 0 (n + 1)‖
```

does not by itself match the hypotheses of the available one-step growth lemmas. So the promised inclusion

```lean
ParameterEscapeLevel n ⊆ ParameterEscapeLevel (n + 1)
```

needs an additional genuine elementary lemma bridging the fixed threshold `2` to the actual escape-radius growth regime, or a different but provably equivalent exhaustion package.

## Honest conclusion

I did **not** keep the attempted source file, because it did not typecheck and I will not leave broken or fake code in the repository.

The smallest honest next theorem would be something like:

```lean
lemma orbit_zero_gt_two_step_mono (c : ℂ) {n : ℕ}
    (h : 2 < ‖orbit c 0 (n + 1)‖) :
    2 < ‖orbit c 0 (n + 2)‖
```

proved from the actual quadratic escape estimates, or else a sourced proof that the exterior is exhausted by the more natural `R c`-superlevel sets and then a checked equivalence back to the requested `2`-threshold formulation.

Until that bridge is formalized, Prompt 83 cannot honestly be marked complete as stated.

## Repository state

No committed Lean source changes were left behind from the failed attempt.
