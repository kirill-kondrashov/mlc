# TASK 62 — Prove finite parapuzzle phase–parameter transport

## Objective

Remove the current source-side blocker by formalizing the first genuine
finite-level parapuzzle theorem. The target is not another generic consumer
interface; it is a moving parameter-plane construction with connected
Mandelbrot slices.

Desired endpoint:

```lean
∃ (W K : ℕ → Set ℂ),
  ConnectednessWindowParameterPieceData c W K
```

for every finitely renormalizable `c ∈ MandelbrotSet`.

## Mathematical content required

Define `W n` from finite moving combinatorial/boundary data and prove:

- ambient openness;
- basepoint membership;
- nestedness or neighborhood-basis shrinkage;
- connectedness of `W n ∩ MandelbrotSet`;
- a phase–parameter correspondence or equivalent transport statement.

The last item must explain the connectedness result; it cannot be supplied as
an opaque assumption that simply reproduces the target structure.

## Source requirement

Select and cite a precise classical parapuzzle theorem from
Douady–Hubbard/Yoccoz/Lyubich/Schleicher technology. Distinguish:

- the published mathematical theorem;
- existing proved Lean ingredients;
- new formalization still required.

## Staged fallback

If the complete provider cannot yet be built, implement the first substantive
nontrivial theorem, such as:

```lean
finite_parapuzzle_slice_connected_of_phase_parameter_correspondence
```

for a concretely defined finite parameter window. Include the actual
phase–parameter map/homeomorphism or transport relation used in the proof, and
state the exact missing basis/shrinkage theorem.

Do not settle for an abstract structure with fields equal to the conclusion.

## Forbidden shortcuts

- no frontier axiom;
- no renamed `ParaPuzzlePieceAt`;
- no `parameterSet` shell;
- no new axiom, `sorry`, or `admit`;
- no fake external-ray or holomorphic-motion theorem;
- no unrelated Böttcher scaffolding;
- preserve existing APIs and do not delete the frontier axiom.

If the first substantive theorem is impossible with current prerequisites, make
no source edits and report the precise missing classical/formal theorem.

## Validation

For edits:

```bash
lake build
lake env lean check_axioms.lean
```

Do not commit.

## Result artifact

Write:

`plan/GPT54_RESULT_62_PROVE_FINITE_PARAPUZZLE_PHASE_PARAMETER_TRANSPORT.md`

The report must say whether a genuine theorem was proved, which source theorem
supports it, and what remains before `FiniteMovingWindowProviderData` can be
instantiated.
