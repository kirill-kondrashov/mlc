# Corrective Prompt 101 -- implement local critical-orbit escape-time coherence

`plan/GPT54_TASK_101_CRITICAL_ORBIT_ESCAPE_TIME_COHERENCE_GATE.md`

Result 104 supplied a concrete parameter-local root germ in
`Mlc/ParameterCriticalOrbitLocal.lean`. Result 101 correctly identified that
the checked fixed-parameter successor mechanism was not yet exported through
that parameter-local interface. This prompt is to **implement that local
packaging**, not to repeat the audit and not to begin the monodromy gate.

Extend `Mlc/ParameterCriticalOrbitLocal.lean` with a concrete theorem of this
shape (minor equivalent binder/order changes are fine):

```lean
theorem exists_parameterCriticalOrbitLocalRootBranch_coherentSucc
    (c₀ : ℂ) (hc₀ : c₀ ∉ MandelbrotSet) :
    ∃ N : ℕ, ∃ V : Set ℂ, ∃ G : ℂ → ℂ,
      V ∈ 𝓝 c₀ ∧ IsOpen V ∧ DifferentiableOn ℂ G V ∧
      (∀ c ∈ V, ‖orbit c 0 (N + 1)‖ > ‖c‖ + 2) ∧
      (∀ c ∈ V,
        (G c) ^ (2 ^ N) =
          logSeriesBottcherApprox c (orbit c 0 (N + 1))) ∧
      (∀ c ∈ V,
        (G c) ^ (2 ^ (N + 1)) =
          logSeriesBottcherApprox c (orbit c 0 (N + 2))).
```

Use the same open ball `V` and branch `G` constructed by the Prompt 104 proof.
Export the already-established strict exterior inequality for every `c ∈ V`.
For the successor identity:

1. raise the level-`N` root identity to the second power;
2. apply the checked theorem
   `logSeriesBottcherApprox_iterate_succ_eq_sq` at the critical value;
3. rewrite its iterate expressions using the existing orbit identities to
   `orbit c 0 (N + 1)` and `orbit c 0 (N + 2)`.

This proves finite escape-time coherence with a **single local branch**: it is
both a level-`N` and a level-`N+1` branch on the same parameter neighborhood.
It does not require comparison of arbitrary separately normalized roots.

This remains a local theorem. Do not claim global continuation, trivial
monodromy, a whole-basin coordinate, parameter rays, or elimination of the
straddling axiom. Do not use `mandelbrot_set_connected`,
`external_ray_map_exists`, global extension contracts, new axioms, `sorry`, or
`admit`. Do not commit.

Run targeted Lean checks and `lake build`, inspect the theorem axiom
dependencies, and replace the current audit-only content of:

`plan/GPT54_RESULT_101_CRITICAL_ORBIT_ESCAPE_TIME_COHERENCE_GATE.md`

with the exact checked result and its limitations. Prompt 102 remains gated
until this theorem is implemented and checked.
