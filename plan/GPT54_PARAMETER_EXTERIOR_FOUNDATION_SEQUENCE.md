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
   Current gate: state and source-check the correct exterior/spherical
   coordinate theorem, then identify a non-axiomatic direct parameter Böttcher
   construction route. It must not use the existing Mandelbrot-connectedness
   axiom in the final no-new-axiom route.

The finite escape-locus route has discharged exterior connectedness, but it
does not itself provide a parameter coordinate, rays/equipotentials, or the
moving-parapuzzle provider. Every stage is a hard gate: record an exact
missing theorem rather than introducing an axiom or placeholder.
