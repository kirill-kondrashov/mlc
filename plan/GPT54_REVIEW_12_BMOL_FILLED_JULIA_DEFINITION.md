# Supervisor Review 12: Intrinsic BMol filled Julia definition

**Verdict:** definition accepted and ready for a small Lean implementation;
normalized-quadratic compatibility is deferred.

Result 12 corrects the central mathematical issue from Result 11.  For a
quadratic-like map represented by global `g.f` and domain `g.U`, the intrinsic
non-escaping set

```lean
{z : ℂ | ∀ n : ℕ, (g.f^[n]) z ∈ g.U}
```

matches the standard definition, includes time zero, and is equivalently the
intersection of the iterate preimages of `g.U`.  The global representation of
`g.f` does not obstruct this definition because every accepted iterate is checked
against the intended domain.  The proposed declarations were also tested with
Lean successfully.

The report's compatibility analysis is important and accepted:

- `parameterToBMol` hides its domain choices in its public specification;
- its actual witness has `U = V = univ`;
- hence its intrinsic non-escaping set is `univ`, not the bounded-orbit set
  `MLC.Quadratic.K c`.

Accordingly no compatibility theorem may be derived from critical-value equality,
and exposing the existing `univ` domains would document the incompatibility rather
than fix it.

The executive decision is adjusted from option (3) to **option (1): the intrinsic
definitions compile and are ready for a small Lean implementation**.  Compatibility
with a normalized quadratic restriction is not a prerequisite for introducing
honest intrinsic definitions.  It is a separate constructor-design task.

The next implementation must remain narrow: add the filled Julia set, its
membership/intersection lemmas, the connected-fiber predicate, the minimal family
shell, and its connectedness locus.  It must not modify or supplement
`parameterToBMol`, attempt straightening, or assert any connectedness theorem.
