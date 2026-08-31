# TASK 51 — Generalize the local-connectivity consumer to moving parameter pieces

## Global context

The live frontier remains:

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

The exact frozen-base statement is not currently matched by a verified
classical theorem. The recommended route is instead:

```text
genuine moving parameter piece family
→ connected relative pieces
→ shrink-compatible local-connectivity consumer
→ migrate downstream code
→ delete the frozen straddling axiom
```

The current consumer in `Mlc/LcAtOfShrink.lean` is hard-coded to:

```lean
Quadratic.ParaPuzzlePieceAt c n
```

This task creates the reusable consumer surface before the genuine parameter
geometry is formalized.

## Deliverable

Add a focused module or carefully extend `LcAtOfShrink.lean` with a generic
piece-family interface and theorem. A suitable shape is:

```lean
structure ParameterPieceFamily where
  piece : ℂ → ℕ → Set ℂ
  piece_open : ∀ c n, IsOpen (piece c n)
  center_mem : ∀ c n, c ∈ piece c n
  relative_connected :
    ∀ {c : ℂ}, c ∈ MandelbrotSet → ∀ n,
      IsConnected (piece c n ∩ MandelbrotSet)
  basis_at :
    ∀ {c : ℂ}, c ∈ MandelbrotSet →
      ∀ U ∈ 𝓝 (⟨c, ‹_›⟩ : MandelbrotSet), ∃ n,
        {x : MandelbrotSet | x.1 ∈ piece c n} ⊆ U
```

The exact structure may differ. Prove a generic theorem yielding:

```lean
LocallyConnectedAt MandelbrotSet ⟨c, hc⟩
```

from the family’s relative connectedness and basis data. If a shrink-to-singleton
package is included, prove the basis theorem generically only when its required
compactness/nesting hypotheses are explicit and genuinely sufficient. Do not
silently reuse facts specific to the current frozen `ParaPuzzlePieceAt`.

Preserve existing APIs and current theorem behavior. The old frozen route may
become a specialization of the new theorem, but the frontier axiom remains in
place for now.

## Constraints

- Do not define the new family using `green_function c (c' - c)`.
- Do not define a piece as an `IsConnected` witness or exact image.
- Do not claim a concrete moving family or parameter external coordinate.
- Do not modify the frontier axiom.
- No `sorry`, `admit`, or new axiom.
- Keep unrelated Böttcher mesh work untouched.
- Do not commit.

## Verification

Run the smallest relevant checks, then:

```bash
lake build
lake env lean check_axioms.lean
```

The axiom frontier must remain unchanged.

## Result report

Write:

`plan/GPT54_RESULT_51_GENERALIZE_LC_CONSUMER_TO_MOVING_PARAMETER_PIECES.md`

Report:

- the exact generic interface;
- the generic local-connectivity theorem;
- compatibility with the current frozen consumer;
- which hypotheses a future genuine moving parapuzzle family must provide.
