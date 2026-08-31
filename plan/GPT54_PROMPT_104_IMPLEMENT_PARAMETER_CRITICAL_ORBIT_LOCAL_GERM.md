Implement the checked parameter-local finite-time root germ:

`plan/GPT54_TASK_104_IMPLEMENT_PARAMETER_CRITICAL_ORBIT_LOCAL_GERM.md`

Result 103 verified that the required full joint near-infinity analytic engine
already exists:

```lean
logSeriesBottcherApprox_differentiableAt_joint
```

in `Mlc/Quadratic/Complex/Bottcher/BottcherJointDeriv.lean`.

Create a focused source module, preferably
`Mlc/ParameterCriticalOrbitLocal.lean`, proving a concrete theorem of the
following shape:

```lean
theorem exists_parameterCriticalOrbitLocalRootBranch
    (c₀ : ℂ) (hc₀ : c₀ ∉ MandelbrotSet) :
    ∃ N : ℕ, ∃ V : Set ℂ, V ∈ 𝓝 c₀ ∧ IsOpen V ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G V ∧
        ∀ c ∈ V,
          (G c) ^ (2 ^ N) =
            logSeriesBottcherApprox c (orbit c 0 (N + 1)).
```

Exact implementation requirements:

1. derive `c₀ ∈ basin_of_infinity c₀` from `hc₀` correctly. In particular,
   first prove the reverse direction

   ```lean
   c ∈ K c → c ∈ MandelbrotSet
   ```

   by reindexing the bounded orbit of the critical value to the bounded orbit
   of `0`; then contrapose it to get `c₀ ∉ K c₀`, and use
   `Quadratic.basin_eq_compl_K`. Do **not** contrapose
   `mem_K_of_mandelbrot`: that existing lemma has the wrong direction for this
   purpose;
2. use `exists_iterate_mem_outside_open_of_mem_basin` at the critical value to
   obtain `N` with the required `‖orbit c₀ 0 (N + 1)‖ > ‖c₀‖ + 2`;
3. shrink to an open parameter neighborhood on which the escaped critical
   orbit stays in an exterior polydisc. Choose the polydisc radius `a` strictly
   below one third of the exterior gap so that the exact hypothesis

   ```lean
   ‖c₀‖ + 3 * a + 2 < ‖orbit c₀ 0 (N + 1)‖
   ```

   of `logSeriesBottcherApprox_differentiableAt_joint` holds;
4. prove differentiability of

   ```lean
   c ↦ logSeriesBottcherApprox c (orbit c 0 (N + 1))
   ```

   by composing the joint differentiability theorem with the parameter-orbit
   graph;
5. replay the explicit ratio/log/exp local-root construction from
   `BottcherLocalRootBranch.lean`. Its raw ratio domain is only known to be a
   neighborhood. For the requested `IsOpen V`, finish by selecting a positive
   metric ball centered at `c₀` contained in that raw neighborhood and restrict
   the root identity and differentiability proof to that ball.

Use a concrete theorem and proof, not a new opaque structure. Import the new
module from `Mlc.lean` only after it compiles. Run targeted checks and inspect
the theorem's axiom dependencies.

Do not claim escape-time independence, global continuation, a whole-basin
coordinate, parameter rays, injectivity, or the target straddling theorem. Do
not use `mandelbrot_set_connected`, `external_ray_map_exists`, the frozen
straddling axiom, a global extension contract, `logCorrectionSeries c c`, new
axioms, `sorry`, `admit`, or commits.

Write:

`plan/GPT54_RESULT_104_IMPLEMENT_PARAMETER_CRITICAL_ORBIT_LOCAL_GERM.md`
