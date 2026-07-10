# Supervisor Review 10: Connected renormalization locus specification

**Verdict:** architecture accepted with two required corrections; proceed to a
small foundation-design audit.

The report correctly repairs Task 09's central error.  The ambient open window
`Λ`, the naive set `Λ ∩ MandelbrotSet`, and the source-defined connectedness /
renormalization loci `M(g)` and `M°` must remain distinct.  On the cited source
record, Theorem 10.15 applies to the root/tip-completed locus `M°`; no equality
with `Λ ∩ M` or the raw family locus should be imported.  The report also gives
the right downstream warning: one compact little Mandelbrot copy is not a
relative neighborhood basis for `LcAtOfShrink`, and Theorem 10.15 supplies no
nesting or singleton-intersection theorem.

Two corrections are required before turning the proposed signatures into Lean.

1. **Fullness is not transported by an abstract subtype homeomorphism.**  A
   homeomorphism `S ≃ₜ MandelbrotSet` preserves intrinsic connectedness, but
   fullness is an extrinsic statement about the complement in `ℂ`.  The proposed
   generic `IsFull` corollary is therefore invalid without substantially stronger
   ambient data (for example, an ambient-plane homeomorphism) or a direct theorem
   about the straightening embedding.  Corollary 10.3 may be formalized as a
   sourced family theorem, but not derived from an arbitrary homeomorphism of
   subspaces.

2. **The connectedness milestone currently depends on an axiom.**  The repository
   occurrence found for connectedness of `MandelbrotSet` is
   `Quadratic/Complex/Axioms.lean:mandelbrot_set_connected`.  Consequently a
   generic homeomorphism-transport lemma is mathematically valid, but using it
   here would not yet add the requested non-axiomatic dynamics foundation.  The
   extra `Nonempty S` hypothesis in the proposed statement is also unnecessary
   once connectedness of the target is supplied.

The first honest milestone should therefore be definition-facing: audit `BMol`
and related structures, introduce only the minimal theorem-faithful family data
that can actually be defined from existing notions, define its connectedness
locus from a non-axiomatic fiber predicate, and prove the definitional membership
equivalence.  If the existing repository does not yet have a suitable filled
Julia set or connected-fiber predicate for `BMol`, the next report must stop at
the exact missing dependency rather than hide it in a `Prop` field named
`quadraticLike`, `motion`, or `properties`.

The decision remains **(2) architecture ready but quadratic-like family
foundations missing**.  The source-level distinction and the negative conclusion
for direct use by `LcAtOfShrink` are accepted.
