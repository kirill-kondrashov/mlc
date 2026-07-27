# Foundation sequence for the parameter exterior

This is the corrected sequence after Results 77--87. It does not treat a
missing global parameter coordinate, a generic planar-complement theorem, or a
Riemann map as an implicit hypothesis.

## Completed and retired gates

1. `GPT54_PROMPT_77_DEFINE_FULLNESS_AND_EXTERIOR_TARGETS.md`
   Completed as a specification/source audit, but its ordinary
   `IsSimplyConnected (MandelbrotSetᶜ)` target is corrected below.

2. `GPT54_PROMPT_78_PROVE_FULL_COMPACT_COMPLEMENT_SIMPLY_CONNECTED.md`
   Retired as mathematically misformulated. An exterior domain such as
   `{z : ℂ | 1 < ‖z‖}` is not simply connected as a subspace of `ℂ`, so a
   full compactum does not give the stated ordinary-simple-connectedness
   conclusion.

3. `GPT54_PROMPT_79_PROVE_MANDELBROT_FULLNESS.md`
   Superseded by Results 85--87: the repository now proves
   `IsConnected (MandelbrotSetᶜ)` non-axiomatically.

4. `GPT54_PROMPT_82_FIND_DIRECT_MANDELBROT_EXTERIOR_SIMPLE_CONNECTEDNESS.md`
   Retired. Ordinary simple connectedness of the exterior is the wrong
   topological target.

5. `GPT54_PROMPT_80_FORMALIZE_UNBOUNDED_RIEMANN_MAP.md` and
   `GPT54_PROMPT_81_BUILD_PARAMETER_EXTERNAL_COORDINATE_AND_ARC.md`
   Retired in their old form. The correct target is an exterior/spherical
   uniformization or a direct parameter Böttcher theorem, not a Riemann map
   from an ordinary simply connected plane domain.

## Active finite escape-locus route

6. `GPT54_PROMPT_83_BUILD_PARAMETER_ESCAPE_EXHAUSTION.md`
   Attempted but incomplete. Result 83 incorrectly treated the fixed-`2`
   one-step estimate as unavailable; it must not be rerun unchanged.

7. `GPT54_PROMPT_86_REPAIR_FIXED_TWO_ESCAPE_EXHAUSTION.md`
   Completed. `Mlc/ParameterEscapeExhaustion.lean` now proves openness,
   nesting, exterior membership, and
   `MandelbrotSetᶜ = ⋃ n, ParameterEscapeLevel n` without a new axiom.

8. `GPT54_PROMPT_84_FINITE_ESCAPE_LEMNISCATE_CONNECTIVITY_GATE.md`
   Attempted but superseded. Result 84 overlooked the reusable
   maximum-modulus separation argument already proved in
   `Mlc/BasinConnected.lean`; critical-value containment is not required for
   exterior-superlevel connectedness.

9. `GPT54_PROMPT_87_REPAIR_ESCAPE_LEVEL_CONNECTEDNESS_MAXIMUM_MODULUS.md`
   Completed. `Mlc/ParameterEscapeExhaustion.lean` now proves every finite
   escape level preconnected and connected by the maximum-modulus argument.

10. `GPT54_PROMPT_85_ASSEMBLE_ESCAPE_EXHAUSTION_CONNECTEDNESS.md`
   Completed. `Mlc/ParameterEscapeExhaustion.lean` now proves
   `IsConnected (MandelbrotSetᶜ)` by the nested connected-union theorem.

11. `GPT54_PROMPT_88_CORRECT_EXTERIOR_UNIFORMIZATION_TARGET.md`
   Completed as a topology audit. Its proposed near-infinity extension package
   is not a next construction step: that structure already requires the
   missing global basin family and boundary data.

12. `GPT54_PROMPT_89_FINITE_PARAMETER_FILLED_LEVEL_CONNECTIVITY_GATE.md`
   Completed as a blocker audit. Compactness, nesting, and the intersection
   characterization are routine consequences of the escape-level package, but
   finite filled-level connectedness splits into two missing ingredients:
   critical-value containment for the parameter orbit polynomials and a
   polynomial closed-lemniscate connectivity theorem.

13. `GPT54_PROMPT_91_PARAMETER_ORBIT_DERIVATIVE_ESCAPE_GATE.md`
   Completed as a blocker audit. The derivative recurrence is available, but
   its first-escape transition is not discharged by the present algebra and
   must not be closed with a global parameter coordinate.

14. `GPT54_PROMPT_92_GAUSS_LUCAS_PARAMETER_ORBIT_CRITICAL_POINT_BOUND.md`
   Completed as an initial audit. Its first reported blocker was discharged
   directly in `Mlc/ParameterEscapeExhaustion.lean` by
   `boundedOrbit_of_orbit_zero` and `mandelbrot_of_orbit_zero`.

15. `GPT54_PROMPT_93_IMPLEMENT_GAUSS_LUCAS_PARAMETER_ORBIT_BOUND.md`
   Completed. `Mlc/ParameterOrbitPolynomial.lean` now proves the Gauss--Lucas
   critical-point location theorem
   `parameterOrbitPolynomial_derivative_root_norm_le_two` without a new axiom.

16. `GPT54_PROMPT_94_PARAMETER_ORBIT_CRITICAL_VALUE_GATE.md`
   Completed as a blocker audit. The Gauss--Lucas critical-point theorem does
   not control critical values, and no checked structural upgrade was found.

17. `GPT54_PROMPT_95_POLYNOMIAL_CLOSED_LEMNISCATE_CONNECTIVITY_GATE.md`
   Gated on an actual Result 94 critical-value theorem. Prove or precisely
   source the closed-disk polynomial-preimage connectivity theorem needed for
   the finite parameter polynomials.

18. `GPT54_PROMPT_96_IMPLEMENT_FINITE_PARAMETER_FILLED_LEVELS.md`
   Gated on Result 94 and Result 95. Define the finite filled levels and prove
   compactness, nesting, intersection with `MandelbrotSet`, and connectedness.

19. `GPT54_PROMPT_90_ASSEMBLE_MANDELBROT_CONNECTEDNESS.md`
   Gated. Result 90 was attempted prematurely and correctly blocked. Do not
   rerun it until a genuine critical-value-containment theorem and the
   still-missing polynomial closed-lemniscate connectivity theorem supply the
   nested compact connected filled levels and their intersection
   characterization; then it should prove `IsConnected MandelbrotSet` without
   `mandelbrot_set_connected`.

20. `GPT54_PROMPT_97_DIRECT_PARAMETER_BOTTCHER_COORDINATE_GATE.md`
   Gated on a checked non-axiomatic `IsConnected MandelbrotSet`. Construct or
   precisely isolate the direct parameter Böttcher/exterior-coordinate theorem;
   do not substitute ordinary plane simple connectedness or a generic Riemann
   map.

21. `GPT54_PROMPT_98_BUILD_PARAMETER_ARCS_AND_MOVING_TRANSPORT.md`
   Gated on a genuine coordinate from Result 97 **or** Result 102. Construct
   parameter equipotential/ray arcs and the phase--parameter transport needed
   by the moving parapuzzle route.

22. `GPT54_PROMPT_99_DISCHARGE_STRADDLING_FROM_MOVING_PROVIDER.md`
   Gated on Result 98. Wire the genuine moving provider through the existing
   adapters and prove the target theorem without the straddling axiom.

Even a successful Prompt 93 is only a critical-point-location result. Prompts
94 and 95 are separately gated hard theorems; neither may be replaced by the
already-proved connectedness of open superlevels.

The finite-filled-level branch is now at a genuine source frontier. Prompt 94
has recorded its exact missing theorem. Prompts 95--97 remain gated and must
not be run until a new critical-value source theorem exists.

## Alternative direct critical-orbit parameter route

23. `GPT54_PROMPT_100_CRITICAL_ORBIT_LOCAL_PULLBACK_GATE.md`
   Completed partially. The fixed-parameter phase-space branch
   `localPullbackRootBranchData_of_iterate_outside` is concrete and checked,
   but it is not a parameter-neighborhood germ.

24. `GPT54_PROMPT_103_PARAMETER_CRITICAL_ORBIT_LOCAL_GERM_GATE.md`
   Completed as an implementation-readiness audit. The checked joint
   differentiability theorem supplies the needed composite analytic engine.

25. GPT54_PROMPT_104_IMPLEMENT_PARAMETER_CRITICAL_ORBIT_LOCAL_GERM.md
   Completed. Mlc/ParameterCriticalOrbitLocal.lean now constructs a concrete
   finite-time parameter-local root germ with no new axiom.

26. GPT54_PROMPT_101_CRITICAL_ORBIT_ESCAPE_TIME_COHERENCE_GATE.md
   Completed. The same local branch is now proved coherent at levels N and
   N + 1, and its uniform exterior estimate is exported.

27. GPT54_PROMPT_102_CRITICAL_ORBIT_PARAMETER_MONODROMY_GATE.md
   Completed as a blocker audit. The repository has no parameter-loop analytic
   continuation or monodromy representation for the local critical-orbit charts.
   Fixed-parameter basin-loop scaffolding does not supply this missing bridge.

28. GPT54_PROMPT_105_PARAMETER_LOCAL_CHART_DATA_AND_HIGHER_LEVEL_LIFTS.md
   Completed. Local parameter branch data now carries coherent root identities
   at every later finite escape level.

29. GPT54_PROMPT_106_PARAMETER_LOCAL_CHART_OVERLAP_TRANSITIONS.md
   Completed. Two charts now differ by a constant root-of-unity multiplier on
   each preconnected overlap with a witness point.

30. GPT54_PROMPT_107_PARAMETER_PATH_CHART_CHAIN.md
   Completed. A compact parameter path now has a finite ordered chart chain
   with explicit adjacent preconnected overlap witnesses.

31. GPT54_PROMPT_108_PARAMETER_LOOP_TRANSITION_PRODUCT.md
   Completed. A chosen finite chart chain for a closed parameter loop now has
   a common-level root-of-unity transition product.

32. GPT54_PROMPT_109_PARAMETER_LOOP_TRANSITION_COMPARISON.md
   **Current gate.** Define canonical local transitions, prove their
   triple-overlap cocycle law, and audit the exact data needed for refinement
   comparison.

33. Future parameter-loop monodromy gate
   Gated on Result 109. Prove product invariance under the required chain
   comparisons and triviality on every loop, or isolate its exact source theorem.

Only if the parameter-loop gate produces a genuine global parameter coordinate
may the flow continue at Prompt 98. It must not use the whole-basin
EscapeTimeIndependentPullbackDataFor contracts as a substitute.

In particular, do not try to evaluate the near-infinity log-series coordinate
at `z = c`: its checked estimates require `‖z‖ > ‖c‖ + 2`, which is impossible
at that evaluation point. Connectedness of `MandelbrotSetᶜ` also does not
trivialize analytic-continuation monodromy.

The finite escape-locus route has discharged exterior connectedness, but it
does not itself prove connectedness of the Mandelbrot set, provide a parameter
coordinate, rays/equipotentials, or the moving-parapuzzle provider. Every
stage is a hard gate: record an exact missing theorem rather than introducing
an axiom or placeholder.
