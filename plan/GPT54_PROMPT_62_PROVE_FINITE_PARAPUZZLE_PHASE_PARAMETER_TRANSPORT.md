Prove the next substantive theorem toward removing
`MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`.

Work from:

`plan/GPT54_TASK_62_PROVE_FINITE_PARAPUZZLE_PHASE_PARAMETER_TRANSPORT.md`

The generic moving-window consumer route is already complete. The missing
source theorem is a genuine finite-level phase–parameter/boundary-motion
transport theorem for quadratic parapuzzles.

## Required theorem target

Construct a non-opaque finite parapuzzle object and prove a theorem of the
following mathematical content:

```lean
theorem finite_parapuzzle_phase_parameter_transport
    (c : ℂ) (hc : c ∈ MLC.Quadratic.MandelbrotSet)
    (hfin : FinitelyRenormalizable c) :
    ∃ (W K : ℕ → Set ℂ),
      ConnectednessWindowParameterPieceData c W K
```

This theorem is acceptable only if `W` is defined from genuine moving
finite-level parameter combinatorics, not by aliasing or relabelling
`ParaPuzzlePieceAt`.

## Substantive requirements

The construction must expose and prove:

1. finite moving boundary/combinatorial data defining each `W n`;
2. ambient openness of `W n`;
3. `c ∈ W n`;
4. nestedness or an explicit neighborhood-basis/shrinkage theorem;
5. connectedness of `W n ∩ MandelbrotSet`;
6. a phase–parameter correspondence or equivalent transport theorem explaining
   why the Mandelbrot slice is connected.

Use a precise classical source (Douady–Hubbard/Yoccoz parapuzzle technology or
an equivalent published theorem) and record the source and exact hypotheses.

## Implementation strategy

First inspect existing definitions for dynamical puzzle pieces, holomorphic
motion, parameter graphs, rays, equipotentials, and components. Reuse only
theorems that are actually proved and mathematically relevant.

If the full theorem is too large for one change, implement the first
nontrivial independently useful stage:

```lean
finite_parapuzzle_slice_connected_of_phase_parameter_correspondence
```

for a concretely defined finite parameter window, together with the openness
and phase–parameter hypotheses it genuinely uses. Then state exactly which
remaining theorem is required for basis/shrinkage.

Do not create a structure whose fields merely restate
`ConnectednessWindowParameterPieceData`; the parameter window must be defined
from actual finite combinatorial/boundary data.

## Hard constraints

- Do not use `green_sublevel_translate_inter_mandelbrot_connected_straddling`.
- Do not use `ParaPuzzlePieceAt` under a new name.
- Do not use `parameterSet` alone as a provider.
- Do not add `sorry`, `admit`, or a new axiom.
- Do not assert a classical theorem as an unproved field.
- Do not resume Böttcher monodromy work.
- Preserve the old frozen API and do not delete the frontier axiom yet.
- Do not commit.

If the repository lacks the prerequisites for the first substantive theorem,
make no speculative edits. Produce a hard-stop report naming the first missing
classical ingredient and the smallest formal module needed to state it
non-opaquely.

Validate any source changes with:

```bash
lake build
lake env lean check_axioms.lean
```

Write the result to:

`plan/GPT54_RESULT_62_PROVE_FINITE_PARAPUZZLE_PHASE_PARAMETER_TRANSPORT.md`
