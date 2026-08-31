# Supervisor Review 17: Analytic quadratic-like family total-space audit

**Verdict:** direction accepted, proposed structure not ready for implementation.

Result 17 makes the essential correction that joint analyticity belongs on the
actual total source space and not on `Λ × ℂ` or the discrete topology of `BMol`.
It also correctly recommends subtype-indexed fibers and separate later layers for
properness, unfolding, and equipment.

Three issues must be corrected first.

1. **The total spaces are not scoped over the parameter domain.** The proposed
   fields allow `totalU` and `totalV` to contain arbitrary points whose first
   coordinate lies outside `parameterSet`. Agreement of sections for
   `c : parameterSet` does not rule out those extra components. The structure must
   state projection containment, or preferably an exact total-space equality,
   such as

   ```lean
   totalU = {p | p.1 ∈ parameterSet ∧ p.2 ∈ (fiber ⟨p.1, ...⟩ : BMol).U}
   ```

   represented in a Lean-friendly way. At minimum it needs
   `Prod.fst '' totalU ⊆ parameterSet` and the analogous law for `totalV`, together
   with the on-domain section equalities.

2. **Derived sections and tautological membership lemmas should not be structure
   fields.** `fiberU`, `fiberV`, and their `mem_..._iff` facts are determined by
   `totalU` and `totalV`. They should be namespace definitions and `[simp]` lemmas
   outside the structure. Making them fields with defaults leaves redundant,
   potentially overridable data in the family object.

3. **The requested exact source audit was not completed.** The report relied on
   Result 10's normalization and said the PDF was consulted only indirectly. Task
   17 explicitly required exact Chapter 10 §42 extraction of tubes, family
   properness, and equipment with locations. Before fixing the Lean fields, the
   worker must inspect the local source text directly and distinguish source data
   from the proposed representation.

There is also a smaller agreement question: `eval_agrees` only on `fiberU` is
reasonable, but the corrected report should say whether the source regards the
joint map as defined on `totalU` only and why a global Lean representative is
harmless.

Decision (1) is therefore not accepted yet. A corrected, directly sourced,
compile-tested skeleton is required before implementation.
