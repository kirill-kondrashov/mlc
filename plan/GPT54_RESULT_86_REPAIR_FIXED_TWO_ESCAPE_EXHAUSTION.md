# GPT-5.4 Result 86 — Repair Fixed-Two Escape Exhaustion

## Outcome

Prompt 86 is now implemented in checked Lean via `Mlc/ParameterEscapeExhaustion.lean`.

## Added package

The module defines

```lean
def ParameterEscapeLevel (n : ℕ) : Set ℂ :=
  {c : ℂ | 2 < ‖orbit c 0 (n + 1)‖}
```

and proves:

1. `isOpen_parameterEscapeLevel`:
   every fixed level is open, by continuity of `c ↦ orbit c 0 (n+1)`.
2. `parameterEscapeLevel_mono`:
   the levels are nested.
   - If `‖c‖ ≤ 2`, one-step growth follows from
     `norm_fc_ge_norm_sq_sub_norm_c` and the inequality
     `x^2 - 2 > 2` for `x > 2`.
   - If `2 < ‖c‖`, the orbit is shifted to the parameter orbit using
     `orbit_param_eq_orbit_zero_succ`, and the existing lower-bound lemma
     `orbit_param_lower_bound_of_norm_gt_two` gives persistence above `2`.
3. `not_mandelbrot_of_mem_parameterEscapeLevel`:
   any parameter whose critical orbit exceeds norm `2` at some finite stage is
   outside `MandelbrotSet`.
   The proof uses `mandelbrotSet_subset_closedBall_two` plus a genuine tail-growth
   estimate for an arbitrary start `z` with `2 < ‖z‖` and `‖c‖ ≤ 2`.
4. `compl_mandelbrot_eq_iUnion_parameterEscapeLevel`:
   ```lean
   MandelbrotSetᶜ = ⋃ n : ℕ, ParameterEscapeLevel n
   ```
   by extracting an index from the unbounded critical orbit and handling the
   impossible zero index explicitly.

## Scope discipline

This result is only an escape-exhaustion theorem package. It does **not** claim
connectedness, path connectedness, fullness, simple connectedness,
uniformization, external rays, a parameter coordinate, or parameter-boundary
arc statements.

## Validation

Validated with:

- `lake build Mlc.ParameterEscapeExhaustion`
- `make build`
- `make check`

No new axioms, `sorry`, or `admit` were introduced.
