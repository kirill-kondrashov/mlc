# Prompt 104 result: parameter critical-orbit local germ

## Status

Completed honestly in checked source.

## What was implemented

Added `Mlc/ParameterCriticalOrbitLocal.lean` and imported it from `Mlc.lean`.

The new module proves:

- `mem_mandelbrot_of_mem_K`
- `mem_basin_criticalValue_of_not_mandelbrot`
- `differentiable_parameterCriticalOrbitGraph`
- `exists_parameterCriticalOrbitLocalRootBranch`

The main theorem establishes that for any `c₀ ∉ MandelbrotSet` there exists a
finite iterate level `N`, an open neighborhood `V ∋ c₀`, and a function
`G : ℂ → ℂ`, differentiable on `V`, such that

`(G c)^(2^N) = logSeriesBottcherApprox c (orbit c 0 (N + 1))`

for all `c ∈ V`.

## Proof route

1. Prove the reverse bridge `c ∈ K c → c ∈ MandelbrotSet` directly from the
   definitions by reindexing the bounded orbit of the critical value to the
   bounded orbit of `0`, handling the initial `n = 0` term separately.
2. Contrapose this bridge to obtain `c₀ ∉ K c₀`, then use `basin_eq_compl_K`
   to place `c₀` in `basin_of_infinity c₀`.
3. Apply `exists_iterate_mem_outside_open_of_mem_basin` at the critical value
   to obtain `N` with `‖orbit c₀ 0 (N + 1)‖ > ‖c₀‖ + 2`.
4. Define the parameter critical-orbit graph `c ↦ (c, orbit c 0 (N + 1))` and
   prove it is differentiable.
5. Compose `logSeriesBottcherApprox_differentiableAt_joint` with this graph on
   an exterior polydisc.
6. Replay the local ratio/log/exp root-branch construction and then shrink the
   raw neighborhood to an open metric ball `V`.

## Validation

The following passed after the implementation:

- `lake env lean Mlc/ParameterCriticalOrbitLocal.lean`
- `make build`
- `make check`
- `./scripts/verify_output.sh`

Axiom inspection remained on the existing global frontier axioms only; Prompt 104
added no new axioms and used no `sorry`.

## Frontier impact

This discharges the local parameter-germ packaging requested by Prompt 104.
It does **not** solve the broader parameter-carving / puzzle-motion frontier from
Prompts 88 / 100 / 103; it supplies the local analytic branch needed for that route.
