# Supervisor Review 09: Canonical Option B parameter piece

**Verdict:** direction accepted; specification not ready.

The ambient renormalization window `W°` is a genuine canonical parameter-domain
object, but its connectedness does not supply the downstream property. The MLC
consumer needs a connected subset of `M` (or a parameter neighborhood whose
intersection with `M` is connected), not merely a connected open window.

The proposed milestone therefore repeats the old gap at a better object:

- `W°` connected by component construction does not imply `W° ∩ M` connected;
- the proposed `CanonicalParameterPieceFamily.connected_inter_M` field is a
  legitimate consumer interface only after construction, but it packages the
  missing theorem and is not itself progress toward proving it.

The cited monograph contains the correct stronger object and theorem:

- Chapter 10 §43 defines the renormalization locus `M°` inside the complex
  window, including root and tip;
- Theorem 10.15 states that `M°` is canonically homeomorphic to the Mandelbrot
  set, hence connected;
- more generally, Theorem 10.1 identifies the connectedness locus `M(g)` of a
  proper unfolded equipped quadratic-like family with `M`, and Corollary 10.3
  states that `M(g)` is connected and full.

This locus, not the ambient window alone, is the candidate connected parameter
piece. The next specification must distinguish `W°`, `W° ∩ M`, and `M°`, and
prove or source every equality/inclusion between them.

Additional cautions:

- proposed Lean `constant` declarations would be axioms if implemented; actual
  definitions or theorem-backed constructions are required;
- the first milestone as written has no useful `LcAtOfShrink` consumer until a
  relative connected locus and nesting/shrinkage are supplied;
- source precision is now sufficient in the local monograph to focus the next
  audit on Theorems 10.1 and 10.15 rather than searching generically for a
  component-selection clause.
