# Current status (2026-08-30)

## Checked frontier

The root declaration `MLC.mlc_conjecture` is sorry-free and its checked
frontier is unchanged:

- `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`
  (parameter-side straddling connectivity);
- `MLC.residualOpenVirtualNearMoleculeAxiom`
  (Dudko Problems 4.3 and 4.4).

The Molecule dependency is pinned to
`385fc36c553947cf125d09848c2a3077fc751209`. The refreshed upstream API is
adapted without adding its witness-level axiom to the root frontier.

## Completed parameter infrastructure

- Prompt 101: checked local successor coherence for the parameter critical-orbit branch.
- Prompt 104: checked local parameter critical-orbit germs off `MandelbrotSet`.
- Prompt 105: checked packaged local chart data and higher-level lifts.
- Prompt 106: checked local overlap transitions by constant roots of unity on preconnected overlaps.
- Prompt 107: checked finite parameter-path chart chains with explicit adjacent overlap neighborhoods.
- Prompt 108 (`Mlc/ParameterCriticalOrbitLoopProduct.lean`): checked a finite common-level transition product.
- Prompt 109 (`Mlc/ParameterCriticalOrbitLoopComparison.lean`): checked quotient-defined local transitions, uniqueness, and the triple-overlap cocycle.

The loop package is deliberately finite. It does not prove product triviality,
chart/refinement independence, homotopy invariance, a global monodromy
representation, or a global parameter Böttcher coordinate. That route is
paused until a geometric parameter object supplies the missing transport data.

## Validation

- `make build` ✅
- `make check` ✅
- `./scripts/verify_output.sh` ✅
- Targeted checks for the parameter path, loop product, and loop comparison modules ✅

## Current decision for `green_sublevel_...`

**Option B is selected:** define a genuine finite-level moving parameter piece
independently of connectedness, rather than trying to prove the frozen
translated-Green intersection by an equivalent witness or motion-image
package.

Option A remains parked because no independently verified theorem in the
current repository or literature import has been shown to target exactly

```lean
IsConnected
  ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

The existing `ParaPuzzlePieceAt` is a frozen-base dynamical translate. It is
not yet a moving parameter wake, ray/equipotential component, or
phase-parameter object, so the classical parapuzzle theorem cannot simply be
rewritten into the current target.

## Active plan: replace the frozen target honestly

### Phase 0 — guardrails (complete)

- Keep the ambient translated Green sublevel connectivity proof.
- Keep the subset and superset strata separate.
- Do not use `ParaPieceCarvedByMotion`,
  `ParaPieceIsMotionImage`, or any `∃ S, IsConnected S ∧ S = target`
  formulation as a discharge; the repository proves these are either
  impossible on the live stratum or equivalent to the target.

### Phase 1 — specify an independent parameter object (next)

Choose one finite depth and the main-cardioid class first, with base parameter
`c = 0`. If that explicit model exposes a genuine boundary/separation
obstruction, record it before attempting a primitive component. Define the
parameter piece from parameter boundary data and a complementary component,
using the existing finite boundary-graph scaffold in
`Mlc/Quadratic/Complex/FiniteParapuzzleBoundary.lean`.

The definition must include:

- actual boundary/ray/equipotential data, not a connectedness field;
- the complementary component containing the base parameter;
- nesting/refinement data;
- a separate theorem target for its relative intersection with `M`.

The first deliverable is a precise object/theorem pair and a comparison
statement, if one can be proved, to the frozen translated-Green target.

### Phase 2 — prove the restricted geometric theorem

For the selected class and finite level:

1. construct the finite parameter boundary arcs and prove their basic
   compactness, closedness, and separation properties;
2. identify the intended parameter component independently of connectedness;
3. prove the phase-parameter correspondence for that restricted family;
4. prove relative connectivity and the nesting/shrinkage facts required by
   `LcAtOfShrink`.

The first restricted theorem is allowed to cover only the selected class. It
must not be generalized to all `c ∈ MandelbrotSet` until the hypotheses and
correspondence are actually established.

### Phase 3 — migrate the root consumer

Adapt `LcAtOfShrink` and the finite/primitive branch consumers to the genuine
parameter-piece family. Only after the new family supplies the required
relative connected neighborhoods should the frozen `ParaPuzzlePieceAt` route
be removed and the straddling axiom deleted.

Success conditions:

- no weaker replacement axiom is introduced;
- the new parameter object is not defined by connectedness;
- `make check` no longer lists
  `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`.

## Direct Route-C status

`Mlc/Quadratic/Complex/Bottcher/BottcherParamMotion.lean` proves a nontrivial
space-holomorphic motion of an explicit connected closed disk, using the
checked near-infinity parametrized Böttcher inverse. This is reusable local
analytic infrastructure, but it is not an equipotential or parapuzzle
boundary and does not identify its image with the frozen target.

Do not resume λ-lemma, Słodkowski, full-basin Böttcher, or finite loop
invariance work for this frontier until Phase 1 fixes a genuine geometric
consumer requiring that machinery.

## Frozen straddling continuation audit

An independent theorem-surface and proof search was completed against the exact
target

```lean
IsConnected
  ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet)
```

The only immediate Lean proof is to rewrite through
`paraPuzzlePieceAt_eq_green_translate` and invoke the older
`MLC.Quadratic.para_puzzle_piece_inter_mandelbrot_connected` axiom. That is an
equivalent opaque replacement and is explicitly not an acceptable discharge.
The axiom-clean facts currently available — connectedness of the un-intersected
translate, connected escape levels, and connectedness of the Mandelbrot
complement — do not imply connectedness after intersection. The missing
ingredient remains a genuine parameter-side phase/component-attachment theorem
for this frozen target; classical moving parapuzzles do not supply that bridge
in the current definitions.

No source theorem was replaced by an unsupported proof, and no new axiom,
`sorry`, or `admit` was added. The straddling axiom remains unchanged pending
an independently formalized bridge or a corrected parameter-piece definition.

## Motivic alternative-direction refresh (2026-08-30)

The canonical external note,
[Pacman renormalization and noncommutative motives](https://github.com/kirill-kondrashov/raw/blob/main/bridge_between_pacman_renormalization_and_noncommutative_motives.md),
and its repository
[audit summary](refs/bridge_between_pacman_renormalization_and_noncommutative_motives.md)
were audited as an exploratory connection to BGT and Efimov, not adopted as a
concrete proof plan. The note itself marks its finite marked-model categories,
refinement system, categorical renormalization, and parameter realization
`Q_n(P)` as additional constructions. Its connectedness and MLC-neighborhood
requirements are not consequences of Efimov's rigidity theorem.

The revised alternative is now a source-backed conditional route using
Efimov, *Rigidity of the category of localizing motives*,
arXiv:2510.17010v1. The canonical raw references are:

- `/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.pdf`
- `/home/kir/pers/raw/refs/efimov-rigidity-category-localizing-motives-2510.17010v1.tex`

Efimov proves the interfaces needed for the categorical middle layer:
`U_loc : Cat^perf -> Mot^loc`, rigidity and dualizability of
`Mot^loc` and `Mot^loc_E` (`th:rigidity_over_Sp_intro`,
`th:dualizability_and_rigidity`), trace-class/nuclear refinement
(`prop:nuclear_equiv_cond`), inverse-limit/internal-Hom descriptions of
motivic morphisms (`th:morphisms_in_Mot^loc_via_limits`,
`th:morphisms_in_Mot^loc_via_internal_Hom`), and equivariant/local-system
motives (`th:G_equivariant_motives`). These results do not imply connectedness
of a parameter locus.

The active alternative is a three-gate program:

1. construct an independently defined topological realization of finite
   marked Pacman data and prove a phase/component-attachment or no-separation
   theorem;
2. construct a finite incidence category, a conservative
   separation-to-idempotent map, and an independently proved
   indecomposability result;
3. prove the exact comparison with the frozen translated-Green target.

For a finite marking group `G_P`, the proposed relative base is the rigid
convolution category `E_P = Loc(BG_P)`. Refinements become exact strongly
continuous `E_P`-linear functors; eventual trace-class behavior makes Efimov's
nuclear and inverse-limit theorems applicable. A general `Mot_Q` local-system
construction is optional and cannot replace the finite geometric gate.

This gives a possible route to a moving parameter-piece replacement, and may
also be useful for the residual virtual near-Molecule package, but it does not
yet identify the frozen target

```lean
{c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet
```

with a motivic parameter locus. The required missing bridge is a conservative
topological realization: a clopen split of a parameter locus must produce a
categorical idempotent or split exact decomposition, and the relevant marked
model/motive must be shown independently to forbid it. `K`, `THH`, `TC`, or
Efimov's universal property alone do not provide this implication. The exact
comparison is mandatory if the named frozen theorem is to be discharged;
moving-piece consumer migration alone is only a fallback.

The detailed source-specific route, stop conditions, and Lean integration order
are recorded in `plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md`. The checked axiom
frontier is unchanged and no source axiom was added or weakened.

The first falsification gate is now checked in
`Mlc/MotivicIntersectionNoGo.lean`: a generic connected/open straddling
intersection rule is false, while a nontrivial clopen split yields a
nontrivial idempotent in the elementary realization `C(X, ℤ)`. This
formalizes the necessary shape of the missing conservative bridge without
claiming a Pacman realization or changing the axiom frontier.

### Single remaining discharge sentence

The one sentence that must replace the current frontier axiom is:

```lean
theorem green_sublevel_translate_inter_mandelbrot_connected_straddling
    (c : ℂ) (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle :
      ¬ ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ⊆ MandelbrotSet)) :
    IsConnected
      ({c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
        ∩ MandelbrotSet)
```

Under the current Efimov plan, the non-circular proof of this sentence must
construct a finite marked model `P(c,n)`, prove its independently defined
realization locus `Q_n(P(c,n))` connected, and prove the exact comparison

```text
Q_n(P(c,n))
  = {c' | green_function c (c' - c) < (1 / 2)^n} ∩ MandelbrotSet.
```

The connectedness step itself is expected to factor through the
phase/component-attachment theorem, conservative separation-to-idempotent
map, and independent motive indecomposability recorded in
`plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md`. Efimov supplies only the
categorical refinement infrastructure; until the construction and comparison
are proved, the declaration remains an axiom.

The categorical interface is now captured without adding a root axiom in
`Mlc/MotivicConnectednessFrontier.lean` as
`MLC.Motivic.GreenSublevelStraddlingMotivicFrontier`. Its
`SeparationReflectingIndecomposable` field abstracts

```text
π₀ End_{Mot^loc_E}(M_n(P))
```

and requires both directions needed for the contradiction: every nontrivial
clopen split of the realization locus maps to a nontrivial idempotent, while
the selected motive endomorphism monoid has no nontrivial idempotent. The
abstract endomorphism monoid is only a Lean placeholder until the actual
relative Efimov motive is constructed; the conditional theorem in that file
proves the existing topological conclusion from the contract.

The first concrete algebraic gate is now proved in
`Mlc/MotivicFiniteIncidence.lean`: integer-valued functions constant along
the edges of a connected finite boundary-incidence graph have no nontrivial
idempotents. The file defines the graph on the finite subtype of boundary
arcs from `FiniteParapuzzleBoundary.lean` and proves
`boundaryIncidenceGraph_connected_iff_carrier_connected`: for this finite
arc model, carrier connectedness is equivalent to connectivity of the
arc-attachment graph. The theorems
`green_sublevel_translate_inter_mandelbrot_connected_of_incidenceMotiveBridge`
and
`green_sublevel_translate_inter_mandelbrot_connected_of_boundaryIncidenceMotiveBridge`
now wire a connected graph (or the concrete boundary graph) and a conservative
bridge `C(Q_n(P), ℤ) → IncidenceEndomorphismRing(G_P)` to the exact frozen
target, with target nonemptiness proved from the base parameter `c`.

The remaining obligations are to construct the finite marked realization and
its connected boundary carrier independently, prove the conservative bridge,
and establish the exact comparison with that realization. No Efimov motive or
root-axiom discharge has been introduced; the frozen straddling axiom is
unchanged.

## Crash recovery

The 2026-08-30 Copilot crash was a Node/V8 heap-exhaustion event, not a Lean
failure. The repository was revalidated afterward; the crash report remains
untracked and is intentionally not part of the source or commit history.
