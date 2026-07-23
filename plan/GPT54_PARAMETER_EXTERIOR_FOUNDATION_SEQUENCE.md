# Foundation sequence for the parameter exterior

This is the corrected sequence after Results 77--86. It does not treat a
missing global parameter coordinate, a generic planar-complement theorem, or a
Riemann map as an implicit hypothesis.

## Completed and retired gates

1. `GPT54_PROMPT_77_DEFINE_FULLNESS_AND_EXTERIOR_TARGETS.md`
   Completed as a specification/source audit.

2. `GPT54_PROMPT_78_PROVE_FULL_COMPACT_COMPLEMENT_SIMPLY_CONNECTED.md`
   Blocked: bundled Mathlib lacks the substantial generic planar-topology
   bridge from a full compactum to a simply connected complement.

3. `GPT54_PROMPT_79_PROVE_MANDELBROT_FULLNESS.md`
   Blocked: the repository has no non-axiomatic global parameter-exterior
   theorem proving `IsConnected (MandelbrotSetᶜ)`.

4. `GPT54_PROMPT_82_FIND_DIRECT_MANDELBROT_EXTERIOR_SIMPLE_CONNECTEDNESS.md`
   Retired. It would repeat the missing global-exterior step found by Result
   79 and cannot independently establish simple connectedness.

5. `GPT54_PROMPT_80_FORMALIZE_UNBOUNDED_RIEMANN_MAP.md` and
   `GPT54_PROMPT_81_BUILD_PARAMETER_EXTERNAL_COORDINATE_AND_ARC.md`
   Deferred. Result 76 already found no usable Riemann-map theorem, and their
   topological prerequisites are unavailable.

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
   Active repair: reuse or extract the `BasinConnected` maximum-modulus
   argument for the entire parameter iterate and the checked outer containment
   `ParameterEscapeLevel 0 ⊆ ParameterEscapeLevel n`.

10. `GPT54_PROMPT_85_ASSEMBLE_ESCAPE_EXHAUSTION_CONNECTEDNESS.md`
   Only after 86 and 87 produce all required checked lemmas, derive
   `IsConnected (MandelbrotSetᶜ)` from the nested union using Mathlib's
   connected-union theorem. Do not claim simple connectedness, uniformization,
   parameter rays, or a parapuzzle boundary arc.

The finite escape-locus route may establish only exterior connectedness. Even
if it succeeds, actual parameter rays/equipotentials and the moving-parapuzzle
provider remain separate unsolved gates. Every stage is a hard gate: record an
exact missing theorem rather than introducing an axiom or placeholder.
