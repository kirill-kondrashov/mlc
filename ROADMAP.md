# MLC research roadmap

## Goal and current invariant

The target is an unconditional theorem

```lean
LocallyConnectedSpace MLC.mandelbrotSet
```

with an axiom frontier limited to Lean's standard foundations. The active proof
must retain the invariant that every declaration is connected to
`MLC.mlc_conjecture`. The graph currently exposes two open mathematical
inputs, the operational forms of Problem 4.3 and Problem 4.4 (the survey states that the problems,
together with the arguments of its §4.1–§4.4, should imply MLC, and does not state them in this
form; `Mlc/Dudko.lean`), and the sixteen lemmas into which
`Mlc/ProgrammeRoot.lean` decomposes them (see the programme tree below).

Problem 4.3 requires pseudo-Siegel a priori bounds and a realization for all
remaining unbounded satellite quadratic-like cases. Problem 4.4 requires
virtual-Molecule completion through partially invariant virtual Julia sets and
phase-parameter transfer. The graph, axiom audit, and absence of
`sorry`/`admit` remain hard validation gates.

## Research method

Each iteration follows the same cycle:

1. Reach the exact boundary of available mathematics and identify the next
   missing theorem or construction.
2. Search the current literature and isolate the closest published theorem,
   definition, and proof dependency.
3. Formalize the smallest reusable interface and prove every generic
   consequence from that interface.
4. Restrict the unresolved parameter class with an independently checkable
   predicate.
5. Add one class to coverage only after its parameter realization has been
   proved and all graph checks pass.

A successful cycle must replace a mathematical
field or open predicate by a proof, a theorem constructor, or a strict logical
classification.

Method notes from Alpöge's remark on his Lean proof of the Riemann hypothesis
(https://alpo.ge/remark.pdf; a narrative, the proof itself is the Lean development):

- **A model situation first.** The remark starts from a setting where the method is known to
  work and transports its mechanism, with the technical work done by the machine. Here the
  model situation is the neutral case (Theorem 4.2, the left loop of Figure 14) and the
  transported mechanism is PS1–PS4 for the right loop (the satellite case, Problem 4.3).
- **The formal development is the artifact.** The statement of every component is a named
  Lean declaration, and the open parts are an explicit list: the 16 fields of
  `ProgrammeInput` and nothing else (`make check` audits the axioms of the root).
- **A timeline of components.** The programme tree and the Progress table play the role of
  the timeline: each lemma has a source, a status and an attack plan.
- **Independent verification.** The remark relies on a full compile, an axiom list, a kernel
  replay and a second checker. For this repository the analogue is a replay of the grid
  certificates and of the programme theorems by an independent kernel; it is not done yet.

## Class hierarchy

The final coverage argument should organize every `c ∈ M` into disjoint or
prioritized classes:

| Class | Expected route | Status |
| --- | --- | --- |
| Hyperbolic/interior parameters | Convex subspace neighborhoods | Handled by the topological kernel |
| Non-renormalizable and positive-core-entropy parameters | Primitive pull-off and principal/puzzle expansion | Published literature; substantial Lean work remains |
| Bounded-type primitive and satellite ql parameters | Uniform ql bounds plus parapuzzle shrinkage | Published literature; substantial Lean work remains |
| Anti-Molecule primitive parameters | Puzzle levels and phase-parameter transfer | Published literature; substantial Lean work remains |
| Satellite types of quadratic growth (`QG_N`) | Near-parabolic renormalization (Cheraghi–Shishikura, Theorem D) | Published preprint; substantial Lean work remains |
| Remaining unbounded satellite ql parameters | Pseudo-Siegel a priori bounds | Problem 4.3 |
| Virtual bounded-period satellite chains | Virtual-Molecule width amplification | Problem 4.4 |
| Virtual near-neutral chains | Pseudo-Siegel regularization and interpolation | Problem 4.4 |
| Exceptional unclassified boundary points | Contradiction or an explicit singleton/control theorem | Must be empty at completion |

Every class definition must use dynamical data such as first-return type,
relative period, renormalization phase, or geometric control. A class may not
be defined by the local-connectivity conclusion itself. The classes of the
table are refined, with their lemmas, in the programme tree below.

## Workstreams

### 1. Combinatorial renormalization

Formalize:

- satellite and primitive Mandelbrot copies;
- the finite chain `M = M^(0) ⊋ M^(1) ⊋ ...`;
- relative periods and cumulative first-return times;
- `1/2`-decorations and the primitive exit copy;
- bounded-period and unbounded-period profiles;
- virtual bounded-type and virtual near-neutral predicates.

The output is a total, independently testable classification interface.

### 2. Dynamical first-return geometry

Formalize:

- genuine small Julia cores and their Cantor alternatives;
- phase-indexed first-return domains;
- finite critical-orbit windows;
- local degree and branch multiplicity;
- partially invariant domains and restricted return maps;
- connected hulls inside the ambient Julia set.

The repository already checks compactness and connectedness of `K_c`, the
inclusion `J_c ⊆ K_c`, minimal connected-hull existence, and the transfer from
a dynamical separation estimate to a parameter-puzzle estimate. The next
theorem must construct the required hull inside `J_c` for a real parameter
class and prove its partial invariance.

### 3. Width and modulus estimates

Replace numerical placeholders with proved geometric quantities:

- conformal annulus modulus;
- collar contribution;
- total and local degree;
- distortion or quasiconformal loss;
- vertical, horizontal, and wave width;
- topology- and degree-dependent thresholds.

The principal target is an alternative:

- amplification to a shallower scale; or
- a uniform lower bound on the accumulated parameter separation cost.

The second branch must make the current harmonic-budget sequence diverge under
an explicit loss control.

### 4. Phase-parameter transfer

Formalize:

- moving puzzle domains;
- holomorphic motions;
- the critical-value section;
- winding-number-one and properness arguments;
- transfer of collars or annulus modulus to parameter pieces;
- connectedness of every transferred parameter piece;
- preservation of the finite return-window error.

The target object is
`ParameterRealization M c b`, including the exact
`ConnectedNest.SeparationEstimate`.

### 5. Virtual-Molecule interpolation

Split Problem 4.4 into two independent branches:

1. long virtual bounded-period satellite chains;
2. virtual near-neutral chains.

Each branch must prove a `VirtualMoleculeAPrioriControl` for its class.
Uniform hyperbolicity may provide an a posteriori explanation, but it may not
replace the a priori control required by the construction.

The final coverage theorem must prove

```lean
∀ c ∈ M,
  c ∈ interior M ∨ A.Eligible c ∨
    Nonempty (VirtualMoleculeAPrioriControl c)
```

for the actual candidate system `A`.

## The programme tree: Problems 4.3 and 4.4 as lemmas

`Mlc/ProgrammeRoot.lean` decomposes the two open inputs of `RootInput` into sixteen
lemmas, the fields of `MLC.Research.ProgrammeInput`, and `MLC.mlc_of_programme` proves in
Lean that the lemmas give `RootInput` and hence MLC, for every geometric dictionary
`G : Geometry` (the assignment of a class, a tower and a virtual tower to each parameter).
The lemmas are hypotheses; what is proved is the logic that joins them. The graph shows
each lemma as a node, and `scripts/programme.py` is the catalogue.

### The case tree

Dudko's argument reduces local connectivity at a boundary parameter `c` to a priori bounds
for the quadratic-like renormalization tower of `c`, case by case. The eight classes, equal
in weight in the profile, and the lemmas that each needs:

| Class (`BoundaryClass`) | Type of the renormalization | Source | Lemmas |
| --- | --- | --- | --- |
| `finite` | not infinitely renormalizable | Yoccoz, Hubbard | Y |
| `neutral` | irrationally indifferent | Theorem 4.2 | N |
| `boundedType` | bounded relative periods | Theorem 4.1 (Kahn; Dudko–Lyubich) | TC, B, T |
| `antiMolecule` | primitive levels far from the Molecule | Kahn–Lyubich, §4.2 | A, T |
| `quadraticGrowth` | satellite types of quadratic growth, `QG_N` | Cheraghi–Shishikura, Theorem D | QG |
| `unboundedSatellite` | unbounded relative periods at satellite levels, outside `QG_N` | **Problem 4.3** | TC′, G, D, T |
| `virtualBounded` | virtual satellite chain of bounded periods, `n ≫ 1` | **Problem 4.4** | VJ, VT1, VD1, VT |
| `virtualNearNeutral` | virtual near-neutral step | **Problem 4.4** | VJ, VT1, VG2, VD2, VT |

### What is proved

The skeleton of §4.1–§4.3 is checked in `Mlc/Research/Degeneration.lean`, with the
degeneration `W_k` of the levels as abstract positive numbers and the geometric
inputs as hypotheses. For the towers of the quadratic-like classes `W_k = W(f_k)` is the
degeneration of (4.1); for the class of Problem 4.3 it is the pseudo-Siegel degeneration
(see "What is read into the survey").

* `aPrioriBounds_of_jumpCap`: a cap on the jumps of the degeneration (`JumpCap C₀ B₀`: a jump
  `W_{m+1} ≥ C₀ W_m` lands below the ceiling `B₀`) and the dichotomy (4.6) with an additive
  error at most linear in the period, `E(p) = A p`, give `sup_k W_k < ∞` for every tower,
  whatever its relative periods. In the second alternative of the dichotomy, a jump by `C₀`,
  the deeper degeneration is below the ceiling, so `W_{k+n₀} ≤ B₀/C₀`; the first alternative,
  iterated at a distance `n₀` with `c 2^{n₀} ≥ 2`, gives `2 W_{k+n₀} ≤ W_k + 2A/c`; both
  bound the sequence.
* `aPrioriBounds_iff_jumpCap`: given the linear dichotomy, a priori bounds hold if and only
  if the jumps are capped, so the cap is the weakest hypothesis of its shape. A uniform
  growth bound (`aPrioriBounds_of_uniform`, the earlier form of Lemma G) is a stronger one:
  it caps the jumps (`jumpCap_of_growth`).
* `aPrioriBounds_of_tails`: the Teichmüller contraction caps the jumps at the levels of
  relative period at most `P₀` (`jumpCap_of_teichmuller`), so the cap is needed only at the
  levels of relative period above `P₀`. The open content of Problem 4.3 is the tail, at large
  relative period, of two estimates that the survey proves for bounded periods.
* `uniformities_necessary`: both ingredients are needed. (i) By `exists_unbounded_of_superlinear`,
  for every monotone, positive, unbounded `h`, the tower with relative periods `k + 2` and
  widths `h(k+1)` satisfies the Teichmüller contraction (the factor `h(P)/h(1)` for relative
  periods up to `P`), a uniform growth bound when `h` grows by a bounded factor, and the
  amplification with the error `p h(p)` (so the dichotomy, with its first alternative at
  every pair of levels), and its degeneration is unbounded. With `h(x) = x + 1` (growth
  factor 2, quadratic error) this is `exists_unbounded_of_growth_dichotomy`: linear is the
  threshold of the error, even with a uniform growth bound. (ii) The tower with relative
  periods `k + 2` and widths `(k+1)!` (jump factor `k + 2` at every level, which the
  Teichmüller contraction allows) satisfies the dichotomy with a linear error, because for
  every threshold `C` the jump alternative covers all levels above `⌈C⌉` and the finitely
  many lower levels need a small `c` only (`exists_unbounded_of_teichmuller_linearDichotomy`):
  its jumps are uncapped (`factTower_not_jumpCap`), and a cap is needed even with a linear
  error. So the inputs of Theorem 4.1 with period-dependent constants leave a gap exactly at
  unbounded relative periods, and Lemmas G and D are the two halves of it, neither redundant.
* `aPrioriBounds_of_bounded`: for relative periods bounded by `P`, the Teichmüller
  contraction and the dichotomy with a period-dependent error suffice (the error takes
  finitely many values): the argument behind Theorem 4.1.
* `aPrioriBounds_of_strongAmplification`: the primitive levels, (4.3) with (4.5).
* `ReturnBudget.ofBound`: a bound `B` on the degeneration is a return budget with constant
  loss, so that the existing kernel (`ParameterRealization`) consumes it.
* `Mlc/Research/ExtremalLength.lean`: the extremal length of a family of curves, each given by
  its length measure, for an area measure; no topology on the underlying space is needed.
  Proved: comparison (`extLength_mono`); the series law, that is Grötzsch's inequality
  (`extLength_series`: curves that cross two disjoint regions in succession have extremal
  length at least the sum); the parallel law (`extWidth_parallel`, and for finitely many
  families `extWidth_parallel_finset`: widths in pairwise disjoint regions add up, which is
  the term `p W(f₁)` of (4.1)); the arithmetic of (4.6) (`extWidth_ge_of_series`: if the
  lift `G′` carries the fraction `1 − δ` of the extremal length of `G`, the subcurves
  `G ∖ G′` have width at least `δ⁻¹ W(G)`, so `C_δ = δ⁻¹ → ∞`); and the pullback law
  (`extWidth_pullback_le`: if `φ` carries the curves of `ΓX` to curves of `ΓY` with area
  multiplicity at most `d`, then `W(ΓX) ≤ d W(ΓY)`, the shape of the growth bound of the
  Teichmüller contraction, and the monotonicity of the width under a conformal map for `d = 1`).
  This is the conformal
  foundation of PS4, of the amplification (4.3) and of TC; the dynamical families remain
  open, and the widths of the towers are not yet extremal widths of such families.
* `Mlc/Research/AnnulusModulus.lean`: the model case of the theory, the round annulus
  `{r < |z| < R}` of the plane with Lebesgue measure, in polar coordinates. The family of radial
  segments, which join the boundary circles, has extremal length `log (R / r) / (2π)`
  (`extLength_radialFamily`); the family of circles, which separate them, has `2π / log (R / r)`
  (`extLength_circleFamily`); the two are reciprocal (`extLength_radialFamily_mul_circleFamily`).
  So the abstract definition is the classical modulus, and the series law of
  `ExtremalLength.lean` gives Grötzsch's inequality for concentric annuli
  (`extLength_radialFamily_add_le`). The upper bounds are the
  Cauchy–Schwarz inequality in polar coordinates, the lower bounds the metric `1 / |z|`.
* `Mlc/Research/RectangleModulus.lean`: the second model domain, the rectangle
  `(x₀, x₁] × (y₀, y₁]` with Lebesgue measure. The family of horizontal segments, which join the
  vertical sides, has extremal length `(x₁ − x₀) / (y₁ − y₀)` (`extLength_horizFamily`) and
  extremal width `(y₁ − y₀) / (x₁ − x₀)` (`extWidth_horizFamily`): the widths of the rectangles
  `G ⊃ G′` of the survey (Figure 13, the estimate (4.6)) are computed, not assumed. The upper
  bound is Cauchy–Schwarz along a segment with Fubini, the lower bound the characteristic
  function of the rectangle.
* `Mlc/Research/NestModulus.lean`: the geometric half of Lemma T, the Grötzsch–Teichmüller
  estimate for the annuli of a nest. For a nest of connected parameter pieces `P₀ ⊇ P₁ ⊇ …`
  around `c`, the loops of the annulus `Pⱼ ∖ cl P_{j+1}` are the `C¹` closed curves in it that
  separate `cl P_{j+1}` from the complement of `Pⱼ` (every path from the first to the second
  meets the loop), recorded by their arc-length
  measures (`ConnectedNest.loops`); their extremal width is the modulus of the annulus.
  `ConnectedNest.sum_extWidth_loops_le`: if `P₀ ⊂ B(c, R)` and the closure of `Pₙ` contains a
  point at distance `δ` from `c`, the moduli of the first `n` annuli add up to at most
  `2π log (4 (R + δ) / δ) / (log 2)²`. The proof is the parallel law for the disjoint annuli and
  the metric `1/|z − c|` on the ring `δ/2 ≤ |z − c| ≤ R + δ`, whose area is at most
  `2π log (4 (R + δ) / δ)`: a loop that stays outside the disk of radius `δ/2` meets every ray
  from `c`, so it has length at least `2π` (the argument of `γ − c` sweeps `(−π, π)`), and a loop
  that enters the disk and reaches distance `δ` crosses the ring and has length at least `log 2`
  (the function `log |γ − c|` sweeps `[log δ/2, log δ]`); both are the area inequality
  `λ(f(S)) ≤ ∫_S |f′|` of Mathlib in dimension one. So pieces with `DivergentModuli` (moduli that
  add up to infinity) shrink to `c` and have the `SeparationEstimate` of every cost
  (`ConnectedNest.nonempty_parameterRealization`).
  `ConnectedNest.sum_extWidth_loops_le_coarse` is Grötzsch's inequality for a coarsening: the
  modulus of `Pₙ ∖ cl P_m` is at least the sum of the moduli of the annuli `Pⱼ ∖ cl P_{j+1}`,
  `n ≤ j < m`, because their loops are loops of the thick annulus and they are disjoint; so
  grouping the levels of a nest (for instance in blocks around the micro-copies of `M`) can only
  increase the moduli. *Faithfulness:* the separating `C¹` loops of an annulus are separating
  curves, so their extremal width is at most the classical modulus (the extremal width of all
  separating curves), with equality expected for annuli with piecewise smooth boundary, as the
  parapuzzle pieces have, which is not proved here. So `DivergentModuli` implies that the classical
  moduli add up to infinity, and, by `transfer_iff_phaseParameter` below, it is equivalent to
  Lemma T itself.
* `Mlc/Research/PhaseParameter.lean`: `Geometry.PhaseParameter`, the phase–parameter relation in
  moduli form (an a priori bound on the tower of `c` gives a nest in `M` around `c` with
  divergent moduli), and `Geometry.transfer_iff_phaseParameter : Transfer ↔ PhaseParameter`. The
  direction `PhaseParameter → Transfer` is the geometric half above; the converse takes the nest
  of `Transfer`, which shrinks because its separation estimate has a divergent budget, and passes
  to a subnest (`DivergentNest.lean`). So the moduli form is a lossless reformulation of Lemma T,
  and what is open is the construction of the nest from an a priori bound.
  `ProgrammeInput.transfer` keeps the hypothesis `Transfer`.
* `Mlc/Research/DivergentNest.lean`: nests with moduli bounded below. The nest of the disks
  `B(0, 2⁻ʲ)` has annuli of modulus at least `log(3/2)/2π`, because the circles of an annulus are
  loops of its family (`loopMeasure_circleLoop`, `extWidth_loopFamily_ge`) and the extremal length
  of the circles is known (`extLength_circleFamily`); so `concentricNest_divergentModuli` shows
  that the definition of the moduli of a nest is satisfiable. More generally, every shrinking nest
  has a subnest with `DivergentModuli` (`ConnectedNest.exists_divergentSubnest`): each piece
  contains a disk around `c` and a later piece lies in the half of it, so the annulus between them
  contains round annuli of modulus at least `log(3/2)/2π`.
* `Mlc/Research/AreaMultiplicity.lean`: the hypothesis of the pullback law, proved for the quadratic
  polynomials. `AreaMultiplicity mX mY φ J d` says that the area `J² mX`, pushed forward by `φ`, is
  at most `d mY`; it is additive over a measurable partition of the domain and multiplicative under
  composition. An injective map that is differentiable on a measurable set has multiplicity `1`
  there with `J = |φ′|` (the area formula of Mathlib, with the determinant `|w|²` of the
  multiplication by `w`), and `z ↦ z² + c` is injective on each of the two half planes that
  `z ↦ −z` swaps, so `f_c` has multiplicity `2` and `f_c^p` has `2ᵖ`
  (`areaMultiplicity_fc_iterate`). So, if `f_c^p` carries the curves of `ΓX` to curves of `ΓY`,
  then `W(ΓX) ≤ 2ᵖ W(ΓY)` (`extWidth_le_pow_two_mul_fc_iterate`, and for loops
  `extWidth_le_pow_two_mul_fc_iterate_of_loops` with `loopMeasure_comp`): the width of a
  pulled-back family grows by at most `2ᵖ`, which has the shape of the Teichmüller contraction of
  the survey (§4.3: growth at most exponential in the relative period). The
  families of the renormalization levels to which it applies, and the quadratic-like restrictions
  of `f_c^p` to domains, are open.
* `Mlc/Research/VirtualShrinking.lean`: what the dynamical estimate of Lemma VT says. For a cost
  with non-negative terms and divergent partial sums, such as the canonical cost of a degeneration
  bound, `VirtualJuliaNest.SeparationEstimate` is equivalent to the shrinking of the virtual hulls to
  their origins (`VirtualJuliaNest.separationEstimate_iff`), and `Geometry.virtualTransfer_hulls_shrink`
  derives that shrinking from `VirtualTransfer`. So the dynamical content of VT is that the diameters
  of the virtual hulls tend to zero, the analogue of the shrinking of the parameter pieces for T; the
  nest and the phase–parameter chart of VT are the rest.
* `Mlc/Research/QuasiInvariance.lean`: the quasi-monotonicity of the extremal width under a change
  of chart.
  `QcEmbedding Ω φ K` is a `C¹` embedding of an open set with invertible derivative and dilatation
  `‖Dφ‖² ≤ K |det Dφ|` at most `K`; an injective holomorphic map with non-vanishing derivative has
  `K = 1` (`QcEmbedding.of_holomorphic`). The area formula of Mathlib gives the hypothesis of the
  pullback law with multiplicity `K` and stretching `‖Dφ‖` (`QcEmbedding.areaMultiplicity`), so
  `extWidth_le_of_qcEmbedding`: if `φ` carries every curve of `ΓX` to a curve that dominates a curve
  of `ΓY`, then `W(ΓX) ≤ K W(ΓY)` (monotonicity of the width under a conformal embedding for
  `K = 1`; invariance for a biholomorphism, by applying it to the inverse). `Separates.image`: a map that
  is continuous and injective on the compact closure of `O`, with `φ '' O` open, carries a loop
  that separates `K` from the complement of `O` to a loop that separates `φ '' K` from the
  complement of `φ '' O` (the first exit time of a path from `φ '' O`). The modulus of an annular
  region (the extremal width of the `C¹` loops in it that separate `K` from the complement of `O`)
  is therefore at most `Kd` times the modulus of every annular region that contains the image
  (`extWidth_loopFamily_le_map`). So the image of a nest is a
  nest (`ConnectedNest.map`), the modulus of each annulus of the image is at least `1/K` times that
  of the original (`extWidth_loops_le_map`), and divergent moduli are transported
  (`ConnectedNest.DivergentModuli.map`). This is the tool that the transport of the moduli between
  the dynamical and the parameter plane needs, for a `C¹` correspondence; a quasi-conformal
  homeomorphism is in general only absolutely continuous on lines, and neither a chart between a
  phase nest and a parameter nest nor the phase nest is constructed.
* `Mlc/Research/Collar.lean`: a quasi-round annulus has a definite modulus. For a level
  `f : U → V` of a renormalization tower with filled Julia set `E = K_f`, the modulus of `V ∖ E`,
  the extremal width of the separating `C¹` loops, is the `C¹` version of `mod⁺(f)`, the reciprocal
  of the degeneration `W(f)` of the survey (4.1): at most the classical modulus and equal to it for
  round annuli, the identification in general belonging to the dictionary; for the annuli of a nest
  it is `D.loops j`. `IsCollar E V Kd r R`: a
  `C¹` embedding `ψ` of dilatation at most `Kd` of a neighbourhood of the closed disk of radius `R`
  such that `E` lies in `ψ(B̄(w₀, r))` and `ψ(B̄(w₀, R))` lies in `V`. The circles of the round
  annulus bound its modulus below by `log (R/r) / 2π` (`extWidth_loopFamily_ge_radii`), the loops
  go to loops of `V ∖ E`, and so the modulus of `V ∖ E` is at least `log (R/r) / (2π Kd)`
  (`IsCollar.ofReal_le_extWidth`): Grötzsch's monotonicity with the quasi-invariance. A nest whose
  annuli all have collars of dilatation at most `K₀` and modulus at least `μ₀/2π` has moduli
  bounded below by `μ₀/(2π K₀)`, hence divergent moduli and shrinking pieces
  (`ConnectedNest.divergentModuli_of_collars`): the form that bounded geometry takes here. The
  collars of the levels of a tower are not constructed.
* `Mlc/Research/RoundAnnulus.lean`: the modulus of the round annulus, exactly. For `0 < r < R` the
  extremal width of the `C¹` loops in `B̄(c, R) ∖ B̄(c, r)` that separate `B̄(c, r)` from the
  complement of `B(c, R)` is `log (R/r) / 2π` (`extWidth_loopFamily_round`): the circles bound it
  below (`extWidth_loopFamily_ge_radii`), and the metric `1/|z − c|` on the ring, of area
  `2π log (R/r)` (`rhoArea_ringMetric_eq`, equal almost everywhere to the metric of the annulus
  off a null circle), in which every separating loop has length at least `2π`
  (`ofReal_two_pi_le_minLength_round`), bounds it above. The same holds for the open ring
  `r < |z − c| < R` (`extWidth_loopFamily_round_open`, a limit of the circles of radius `s < R`),
  the annulus of a round level of a `LevelTower`, whose degeneration is therefore
  `2π / log (R/r)` (`LevelTower.width_eq_of_round`). So the `C¹` modulus agrees with the classical
  one on the round annuli, the model that the collars compare with.
* `Mlc/Research/NestRate.lean`: the rate of the shrinking. A Teichmüller-type estimate, with the
  non-optimal constants of the metric `1/|z − c|`, in the form
  of a theorem about nests (`ConnectedNest.closure_piece_subset_closedBall_of_sum`): if the
  closure of the first piece lies in `B̄(c, R)` and the first `n` annuli have total modulus at
  least `s`, with `κ s ≥ log 8` and `κ = (log 2)² / 2π`, then the closure of the piece `n` lies in
  `B̄(c, 8 R e^(−κ s))`. Hence moduli bounded below by `μ` give the pieces `n ≥ N` radius at most
  `8 R e^(−κ μ n)` (`closure_piece_subset_closedBall_of_uniform`), and uniform collars give the
  geometric decay `exp(−κ μ₀ n / (2π K₀))`
  (`closure_piece_subset_closedBall_of_collars`). The statement that a nest of divergent moduli
  shrinks (`DivergentModuli.shrinking`) becomes quantitative; the rate is that of bounded
  geometry, and the geometric bound is what the construction of the nest has to supply.
* `Mlc/Research/LevelTower.lean`: the degeneration as the reciprocal modulus of an annulus, and what
  follows. `LevelTower` extends `WidthTower` by the filled Julia sets `K_k` and the range domains
  `V_k` of the levels, with `W_k = 1 / mod(V_k ∖ K_k)` (the survey (3.2), (4.1)), the modulus being
  the extremal width of the `C¹` loops that separate `K_k` from the complement of `V_k`: at most the
  classical modulus, and equal to it for round annuli. The sets are data of the dictionary: nothing
  ties them to the dynamics of `f_c`, and every width tower is realized by round levels
  (`WidthTower.exists_levelTower` in `RoundTower.lean`), so the structure has no dynamical content by
  itself and the hypotheses below are meaningful for the filled Julia sets and range domains of
  quadratic-like restrictions. A collar of the
  annulus of a level bounds its degeneration by `2π Kd / log (R/r)` (`LevelTower.width_le_of_collar`),
  so Lemma G follows from collars at the jump levels: if at every level that follows a jump by the
  factor `C₀` the annulus has a collar of dilatation at most `K₀` and modulus at least `μ₀/2π`, the
  jumps are capped by `2π K₀ / μ₀` (`LevelTower.jumpCap_of_collars`), and with a linear dichotomy
  the tower has a priori bounds (`LevelTower.aPrioriBounds_of_collars`). This is the reading of PS4
  ("bounded by the uniform quasi-conformal geometry of the pseudo-Siegel disks") as a precise
  geometric hypothesis with a proved consequence; that the pseudo-Siegel disks give such collars at
  the jumps is proposed and open, and the same theorem serves the virtual levels of Lemma VG2.
  `Geometry.PhaseParameterComparison` is the form in which the phase–parameter relation is used at
  the renormalization levels: from a degeneration bound on the tower of `c`, a realization of the
  tower by the annuli of its levels and a nest in `M` around `c` such that the modulus of each level
  is at most `Kd` times the modulus of the corresponding annulus of the nest. With it Lemma T
  follows (`Geometry.transfer_of_comparison`): the moduli of the levels are at least `1/B`, so the
  moduli of the nest are at least `1/(B Kd)`, they add up to infinity and the pieces shrink. A
  quasi-conformal chart between the annuli gives the comparison (for a `C¹` chart this is
  `extWidth_loopFamily_le_map`); the realization, the nest and the chart are what is open. The
  comparison is a statement about the dictionary: it is vacuous for a dictionary without towers.
* `Mlc/Research/CollarCriterion.lean`: the chain from the annuli of a nest to the local connectivity
  at its center, closed at a point. A set is locally connected at the center of a connected nest
  whose moduli add up to infinity (`ConnectedNest.locallyConnectedAt_of_divergent`, the Yoccoz
  criterion). With a uniform lower bound `w` for the moduli and the first piece in the disk of
  radius `R` around `c`, for every `ε > 0` some piece of depth at most
  `max (log 8, log (8R/ε)) / (κ w) + 1`, `κ = (log 2)² / 2π`, is a connected neighbourhood of `c`
  inside the disk of radius `ε` (`exists_relativePiece_of_uniform`): a logarithmic modulus of local
  connectivity. Uniform collars give `w = μ₀ / (2π K₀)` (`locallyConnectedAt_of_collars`,
  `exists_relativePiece_of_collars`); the phase–parameter comparison with a degeneration bound `B`
  gives `w = 1 / (B Kd)` (`Geometry.locallyConnectedAt_of_comparison`,
  `Geometry.exists_relativePiece_of_comparison`). The whole chain is
  `Geometry.locallyConnectedAt_of_collars_and_comparison`: collars of dilatation at most `K₀` and
  modulus at least `μ₀/2π` at the jumps of a level tower of `c`, the linear dichotomy for it, and the
  comparison give the local connectivity of `M` at `c`. The collars, Lemma D and the comparison are
  the explicit geometric statements that are open; the concentric nest has uniform collars
  (`concentricNest_collars`), so the hypotheses of the criterion are satisfiable.
* `Mlc/Research/Dimension.lean`: the dimension of the fractal against the smooth curves of the
  moduli. The image of a `C¹` loop has Hausdorff dimension at most `1` (`IsLoop.dimH_range_le`), so
  countably many loops cover no set of larger dimension. A `C¹` embedding with invertible
  derivative is locally bi-Lipschitz, so it preserves the dimension of every subset of its domain
  (`QcEmbedding.dimH_image`), whatever its dilatation, and no `C¹` chart carries a smooth curve onto
  a fractal. A `K`-quasi-conformal map distorts the dimension within the bound of Astala (1994:
  dimension `d` goes to at most `2Kd/(2 + (K−1)d)`; not formalized), which is below `2` for `d < 2`,
  so a quasi-conformal map of finite dilatation never carries a set of dimension below `2` onto a
  set of dimension `2`. The charts of `QuasiInvariance.lean` and `Collar.lean` compare the moduli of
  annuli, which are open sets, and say nothing about the dimension of the sets that the annuli go
  around. An
  `α`-Hölder parametrization of a set of dimension `d` by an interval has `α d ≤ 1`
  (`holder_mul_le_one`). `ShishikuraDimension` states Shishikura's theorem (the boundary of `M` has
  Hausdorff dimension `2`; published, a hypothesis here), and gives that the boundary is not covered
  by countably many `C¹` loops, is not the `C¹` image of a set of dimension below `2`, and has no
  parametrization by an interval that is `α`-Hölder with `α > 1/2`
  (`ShishikuraDimension.holder_exponent_le_half`). For the kernel of a nest: divergent
  moduli leave a point, of dimension `0` (`ConnectedNest.dimH_kernel_eq_zero_of_divergent`), and a
  kernel of positive dimension contains a point other than the center, so the moduli add up to a
  finite bound (`ConnectedNest.sum_extWidth_loops_bounded_of_dimH_kernel_pos`); the kernel of a
  given nest need not be the fiber of the parameter (Schleicher), which the dynamics defines.
* `Mlc/Research/PeanoObject.lean`: the same in the category of compact Hausdorff spaces, next to
  the categorical root. `IsPeanoObject X`: `X` is an epimorphic image of the interval (the
  epimorphisms of `CompHaus` are the surjections), and, the epimorphisms being effective, a regular
  quotient: the coequalizer of its kernel pair, a closed equivalence relation on the interval
  (`IsPeanoObject.exists_regularEpi`; for `M` it is the kernel pair of the chosen parametrization,
  and the landing relation of the rays, which lives on the circle of angles and gives the
  pinched-disk model, is a different statement that is not formalized). A Peano object is locally
  connected
  (`IsPeanoObject.locallyConnectedSpace`: a surjection of a compact space onto a Hausdorff space is a
  quotient map, and quotients of locally connected spaces are locally connected). Given the
  Hahn–Mazurkiewicz theorem (`HahnMazurkiewicz`, the converse for metrizable continua; published,
  not formalized) and the connectedness of `M` (Douady–Hubbard), `Categorical.MLCConjecture` holds
  exactly when `mandelbrotCompHaus` is a Peano object, exactly when it is a regular quotient of the
  interval (`mlc_iff_peano`, `mlc_iff_regularEpi`). Given Shishikura's
  theorem, no epimorphism from the interval onto `boundaryCompHaus` is `α`-Hölder with `α > 1/2`
  (`ShishikuraDimension.holder_exponent_le_half_of_epi`): the parametrization of the boundary that
  MLC provides is wild.

The assembly (`ProgrammeInput.completion`, `.problem43`, `.problem44`, `RootInput.ofProgramme`,
`mlc_of_programme`) uses only the three kernel axioms.

### What is read into the survey

The survey states the cases, Theorems 4.1 and 4.2, the two problems, and, for Problem 4.4,
the strategy of partially invariant virtual Julia sets. It does not state the lemmas TC′, G,
D, VT1, VD1, VG2, VD2. They are the reading proposed here, from the place where the proof of
Theorem 4.1 stops: its two uniformities fail for unbounded relative periods, the factor
`Δ^p` of the Teichmüller contraction (§4.3: "Alternative (ii) is prevented by the Teichmüller
contraction") and the additive error `O_{p_n}(1)` of (4.3) (§4.2: "the period `p_n` is
assumed to be big but still bounded"). The pseudo-Siegel disks of Theorem 4.2 are the
survey's tool for the near-neutral case, and the right loop of Figure 14 is its strategy for
the satellite case. Whether pseudo-Siegel disks give the jump cap and the linear
dichotomy is the question that Problem 4.3 asks.

A literature pass (arXiv sources, read in the text) sharpened the reading:

* **The widths of Problem 4.3 are pseudo-Siegel widths.** The quadratic-like degeneration
  `W(f_k)` is unbounded in some classes of unbounded satellite type: Sørensen's examples,
  and the class `QG_N` of Cheraghi–Shishikura (arXiv:1509.07843, abstract and §1.4), lack
  a priori bounds. A bound on `W(f_k)` for every unbounded satellite tower would be false.
  The survey asks for *pseudo-Siegel* a priori bounds, with the invariant degeneration of the
  parabolic fjords consumed by the disks (§4, before §4.1). So the tower of the class carries
  the pseudo-Siegel degeneration, and Lemmas TC′, G and D are about it. In the neutral case
  the bounds are uniform in the size of the continued-fraction entries (Dudko–Lyubich,
  arXiv:2210.09280, Theorems 1.1–1.3).
* **The Teichmüller contraction is published for bounded periods.** Dudko–Lyubich,
  arXiv:2309.02107, Proposition 2.7, gives `W(Y_n ∖ X_n) = O(Δ_P^n)` with `Δ_P` depending on
  the bound `P` of the relative periods; no source gives a factor uniform over unbounded
  periods. Lemma TC is therefore stated for bounded type, and Lemma TC′ is the version for
  the pseudo-Siegel degeneration (no regularization is needed away from rotation number 0).
* **The error of the dichotomy is not given as a function of the period.** The thresholds
  (`M(p)` in Kahn's Theorem 3.1, `C_{δ,P}` in the Wave Lemma estimate, the threshold of the
  Covering Lemma, `C ≫_{p_n} 1` in §4.1 of arXiv:2309.02107) depend on `p` implicitly. A
  decomposition with a linear topological error exists (Kahn–Lyubich, arXiv:2601.21905,
  Theorem 3.9: `W(S) − O(|χ(S)|) ≤ 2 ∑ W(α) ≤ W(S)`, an error `O(p)` for a disk with `p`
  holes), which is the evidence for the linear error of Lemma D, but it is not the dynamical
  dichotomy. By `uniformities_necessary`, a superlinear error does not suffice, so the rate
  in `p` is a genuine part of Problem 4.3.
* **Partial results.** The class `QG_N` (Cheraghi–Shishikura, Theorem D; for example
  `p_i = ±1`, `q_{i+1} ≥ q_i²`) has local connectivity of `M` by near-parabolic
  renormalization, and is the published class `QG`; Levin proves rigidity under a faster
  growth of the denominators. Dudko–Lyubich (arXiv:2309.02107, Theorems A–B) treat all
  bounded relative periods. For Problem 4.4, Kahn–Kapiamba–Lyubich (arXiv:2606.27272,
  "MLC for parabolically bounded primitive renormalization", Theorems A and C) prove a
  priori bounds and MLC for primitive types that can approach the cusp of `M`, and describe
  the general virtual renormalization as forthcoming. The sector bounds of Variation I (the
  source [19] of the survey) are cited as a manuscript and were not found on arXiv; Variation
  II (arXiv:2509.23031) extends the pseudo-Siegel bounds to `ψ^•`-quadratic-like Siegel
  maps.

### Attack plans

Each lemma is attacked separately; its proof lowers the uncertainty of every class that
needs it, by its share of the class (a class with `m` lemmas gains `1/(8m)` of the classes
component per proved lemma). Statements marked *heuristic* are the proposal of this
roadmap, not claims of the survey.

* **T, VT (transfer).** The Kahn–Lyubich quasi-additivity law turns a priori bounds into
  lower bounds on the moduli of the annuli between nested pieces, and Grötzsch's inequality
  shrinks the pieces when the moduli add up (`ConnectedNest.SeparationEstimate` with a
  divergent budget is already checked). Grötzsch's inequality is proved for the extremal
  length of abstract length measures (`ExtremalLength.lean`: series and parallel laws).
  First step (done, `AnnulusModulus.lean` and `RectangleModulus.lean`): the moduli of the round
  annulus and of the rectangle in the plane as extremal lengths, in polar and in Cartesian
  coordinates (the Yoccoz package uses
  a Gaussian weighted area as a proxy, which changes under conformal maps). Second step (done,
  `NestModulus.lean`, `PhaseParameter.lean`): the Grötzsch–Teichmüller estimate for the annuli of
  a nest of parameter pieces, so that T follows from the phase–parameter relation in moduli
  form (`Geometry.PhaseParameter`, a nest in `M` whose moduli add up to infinity) and, by a
  subnest, is equivalent to it (`transfer_iff_phaseParameter`); the proof
  is checked for general open pieces, with the area inequality in dimension one for the
  argument and the logarithm of `γ − c`, with no Teichmüller bound for a general annulus and no
  conformal invariance needed. Third step (done, `QuasiInvariance.lean`): the extremal width, and
  the moduli of a nest, are quasi-monotone under `C¹` embeddings of dilatation at most `K` (the
  width of a family is at most `K` times that of a family containing the images of its curves;
  `K = 1` for a holomorphic embedding), with divergent moduli transported
  (`ConnectedNest.DivergentModuli.map`). Fourth step (done, `Collar.lean`): a level whose annulus
  has a collar, a quasi-round annular chart of dilatation `Kd` and modulus `log (R/r) / 2π`, has
  modulus at least `log (R/r) / (2π Kd)` (`IsCollar.ofReal_le_extWidth`), and a nest with uniform
  collars has divergent moduli (`ConnectedNest.divergentModuli_of_collars`), with the modulus of
  the round annulus exactly `log (R/r) / 2π` (`RoundAnnulus.lean`) and the pieces shrinking at the
  geometric rate `exp(−κ μ₀ n / (2π K₀))` (`NestRate.lean`, a Teichmüller-type estimate). Fifth step (done,
  `LevelTower.lean`): the degeneration of a level is the reciprocal modulus of its annulus, collars
  at the jump levels cap the jumps (Lemma G in the reading of PS4), and the phase–parameter
  comparison of the moduli of the levels with the moduli of a parameter nest gives Lemma T
  (`Geometry.transfer_of_comparison`). Sixth step (done, `Dimension.lean`): the dimension of the
  fractal against the smooth curves: `C¹` charts preserve the Hausdorff dimension, quasi-conformal
  maps of finite dilatation distort it within Astala's bound and never carry a set of dimension
  below `2` onto a set of dimension `2`, and the boundary of `M` has no parametrization by an
  interval better than `1/2`-Hölder (given Shishikura's theorem). Seventh step (done,
  `CollarCriterion.lean`): the chain closes at a point, collars at the jumps, the linear dichotomy
  and the comparison give the local connectivity of `M` at `c` with a logarithmic scale
  (`Geometry.locallyConnectedAt_of_collars_and_comparison`). Next: `PhaseParameter` itself (the
  phase–parameter
  relation of Lyubich (§3.9) with the quasi-additivity law), which compares the moduli of the
  dynamical annuli of the tower with the parameter annuli; that correspondence is
  quasi-conformal and comes with no `C¹` chart, so the construction of the nest from the bound
  is what stays open. VT has the same shape with the dynamical hulls of
  `VirtualJuliaNest.SeparationEstimate` instead of annuli around the point; its geometric half is
  not yet written. Risk: the conformal geometry is not in Mathlib.
* **Y, TC, B, A, N, QG (published).** Formalize the cited theorems in the form of a parameter
  realization or of the estimate. Y is Yoccoz's puzzle theorem; TC is the Teichmüller
  contraction of §4.3; B, A and N are long research papers; QG is the 71-page theorem of
  Cheraghi–Shishikura. They are listed so that the size of the formalization gap is visible;
  they are not near-term targets.
* **TC′ (pseudo-Siegel contraction).** *Heuristic:* at the levels of relative period at most
  `P` the pseudo-Siegel degeneration is the quadratic-like one (no regularization away from
  rotation number 0, §4.4), so TC′ is TC applied level by level; the new content is the
  compatibility of the regularization of a level with the preceding level (PS1). The
  pullback estimate for extremal widths is proved (`extWidth_pullback_le`: `W(ΓX) ≤ d W(ΓY)`
  for a map of area multiplicity at most `d`), and its hypothesis is proved for the iterates of
  `f_c` (`extWidth_le_pow_two_mul_fc_iterate`: multiplicity `2ᵖ`); the next step (proposal) is its
  application to the families of the renormalization levels, with `d = 2^p`.
* **G (jump cap).** In alternative (ii) of §4.3 the degeneration of the deeper level jumps by
  `C_δ`. The Teichmüller contraction excludes the jump while its factor `Δ^p` stays below
  `C_δ`, which fails for unbounded `p`. The recursion needs only that a jump lands below a
  ceiling (`aPrioriBounds_iff_jumpCap`). *Heuristic:* alternative (ii) comes from the
  combinatorially invariant rectangles (Figure 13), and in the neutral case the pseudo-Siegel
  disks are constructed to consume the invariant degeneration (Theorem 4.2, the left loop of
  Figure 14), so that the deeper degeneration in a jump is bounded by the uniform
  quasiconformal geometry of `Ẑ^{-1}` and `Ẑ^0`. The neutral case is the model situation, and
  the satellite case is the right loop of Figure 14, the antirenormalization relative to `β`
  (PS1–PS3). First step (proposal): the almost-invariance with a geometric error (PS2) for a
  sequence of holomorphic self-maps of a disk, where Mathlib's Schwarz lemma applies; then
  the absorption (PS4) as an inequality between extremal widths, whose arithmetic (4.6) is
  proved (`extWidth_ge_of_series`).
* **D (linear dichotomy).** The survey attributes the additive error `O_p(1)` to a variant
  of the thin–thick decomposition (§4.1) and says that pseudo-Siegel disks are built to
  consume most of the invariant degeneration (§4, near-neutral levels; PS4). *Heuristic:*
  the invariant degeneration is the part that the decomposition cannot bound uniformly in
  `p`, and the rest is controlled by the Wave Lemma. The statement asks for an error at most
  linear in `p` (each of the `p` small Julia sets contributes a bounded error), the sharp
  threshold of the recursion. First step (proposal): state PS4 as an inequality between
  extremal widths and check that it gives the linear error by the argument of §4.3. The
  main term `p W(f₁)` of the amplification is the parallel law (`extWidth_parallel_finset`);
  what remains is the error, that is the thin–thick decomposition with a linear error in the
  dynamical setting.
* **VJ.** The minimal connected hull in `K_c` of the Cantor small Julia set and the critical
  return window exists in Lean (`VirtualJuliaNest.carrier`); the lemma is that it lies inside
  `J_c` and is partially invariant. First step (proposal): the real parameters, where the
  MLC is known (§4.3 with §4.2, [14]), as a test of the statement.
* **VT1, VD1.** *Heuristic:* the virtual levels of a bounded chain behave like the satellite
  levels of Theorem 4.1, with the critical orbit contained in the hull only up to a finite
  number of returns, so that the Teichmüller contraction (VT1, shared with the near-neutral
  subcase) is applied to a partially invariant system. First step (proposal): the first
  return map to the virtual hull and its degree.
* **VG2, VD2.** The near-neutral step is a big relative period in the virtual chain; the
  cap at large relative period and the linear error are those of G and D for the virtual hull,
  after the pseudo-Siegel regularization (Figure 14, left loop). They wait for G and D.

The abstract extremal length, its laws, the moduli of the round annulus and of the rectangle, the
Grötzsch–Teichmüller estimate for nested annuli, and the quasi-invariance of the moduli under `C¹`
embeddings of bounded dilatation exist (`ExtremalLength.lean`, `AnnulusModulus.lean`,
`RectangleModulus.lean`, `NestModulus.lean`, `QuasiInvariance.lean`). What the lemmas that depend
on conformal geometry still need is the link between them and the dynamics: the correspondence
that carries the moduli of the dynamical annuli of a tower to the parameter plane
(`Geometry.PhaseParameter`), then the families of curves of a quadratic-like map. That is the
first real step of every route.

### Rays, the lamination and tuning

The formalization proves local connectivity through connected parameter nests (the Yoccoz
scheme: nested connected neighbourhoods that shrink to the point), and no external ray enters it.
Rays and laminations are classical and are not formalized (they need the Riemann map of the
complement of `M`, which Mathlib does not have). They give equivalent forms of the goal and a
precise description of the points that stay open.

**Equivalent forms of MLC** (Carathéodory; Douady–Hubbard; Thurston; Schleicher):

1. *Rays.* The inverse of the Douady–Hubbard map `Φ_M : ℂ ∖ M → ℂ ∖ closed unit disk` extends
   continuously to the circle, so every parameter ray `R_M(t)` lands and the landing map is
   continuous.
2. *Lamination.* `M` is homeomorphic to the quotient of the closed disk by the quadratic minor
   lamination: `t ∼ t'` exactly when `R_M(t)` and `R_M(t')` land at the same point. On rational
   angles the relation is known (Douady–Hubbard, Thurston); MLC says that the lamination is the
   whole landing relation.
3. *Fibers.* The fiber of `c` is the set of the points that no pair of rational rays landing
   together separates from `c`. `M` is locally connected exactly when every fiber is a point
   (Schleicher, *On fibers and local connectivity of Mandelbrot and Multibrot sets*).
4. *Peano parametrization.* `M` is locally connected exactly when it is a continuous image of the
   interval (Hahn–Mazurkiewicz, given that `M` is a continuum); the landing map of the rays then
   parametrizes the boundary. In `CompHaus` this is an
   epimorphism from the interval onto `M` (`Mlc/Research/PeanoObject.lean`, `mlc_iff_peano`, given
   Hahn–Mazurkiewicz and the connectedness of `M`).

**The fractal against the smooth curves.** The boundary of `M` has Hausdorff dimension `2` and
topological dimension `1` (Shishikura, 1998), and a `C¹` or Lipschitz curve has dimension at most
`1`. Two consequences are checked in `Mlc/Research/Dimension.lean`, given Shishikura's theorem as a
hypothesis: the boundary is not a countable union of smooth arcs, and a parametrization of it by
the interval, such as the landing map of the rays, is at best `1/2`-Hölder, so any Hölder control
of the landing map has an exponent at most `1/2` (`ShishikuraDimension.holder_exponent_le_half`,
and `holder_exponent_le_half_of_epi` for the epimorphisms of `CompHaus`). The moduli of the
development are measured with `C¹` loops, which see a fractal kernel only as a set that is not a
point: divergent moduli leave a point of dimension `0`, and a kernel of positive dimension forces a
finite total modulus. `C¹` charts preserve the Hausdorff dimension (`QcEmbedding.dimH_image`), and
quasi-conformal maps of finite dilatation distort it within Astala's bound (1994; not formalized),
which is below `2` for a set of dimension below `2`: no such map carries a smooth curve, or any set
of dimension below `2`, onto a fractal of dimension `2`. The comparisons of the programme relate
annuli, which are open sets, and say nothing about the dimension of the sets that the annuli go
around. Dimension `2` is compatible with area `0` and with
positive area, so the dimension decides neither the area of the boundary nor the shrinking of the
nests, which is the content of Problems 4.3 and 4.4.

**Which landing points stay open.** The fibers of the parameters that are not infinitely
renormalizable are points (Yoccoz, Hubbard), and the lemmas Y, N, B, A and QG give the same for
the other published classes, so the rays whose impressions meet those classes land. A ray that
fails to land has an impression that is a non-trivial continuum, contained in a non-trivial
fiber, and a non-trivial fiber consists of infinitely renormalizable parameters of the classes
`unboundedSatellite`, `virtualBounded` and `virtualNearNeutral`. So the rays land at points where
local connectivity is known, except possibly at the parameters of Problems 4.3 and 4.4. This is
what the tree decomposes: Lemmas TC′, G, D (and VT1, VD1, VG2, VD2) bound the degeneration, Lemma
T turns the bound into shrinking nested parameter pieces, shrinking pieces make the fiber a
point, and a trivial fiber is the landing of the ray. The ray form adds no hypothesis; it
locates the lemmas in the plane of angles (the open angles are those of the infinitely
renormalizable parameters outside the published classes, a set of unknown measure) and it is the
form in which the final statement would be read.

**Tuning: exact combinatorial similarity, no metric one.** Tuning `τ_w : M → M_w ⊂ M` by a
hyperbolic center `w` (Douady–Hubbard straightening) is a homeomorphism onto a little copy, and
the copy is cut out of `M` by a renormalization window, so `M` is locally connected at a point of
`M_w` other than its root exactly when it is at the untuned point. For an infinitely
renormalizable `c' = τ_{w_1} ∘ τ_{w_2} ∘ …` this reduces local connectivity to the shrinking of
the nested copies, `diam M_k → 0`, that is, to the a priori bounds together with the transfer
Lemma T. The copies are exactly similar to `M` in the combinatorics (the lamination of the copy
is the substitution of the lamination of `M`) and only asymptotically similar in the metric: a
homeomorphism does not control the diameter of the image of a set (a Hölder estimate does not
iterate to a contraction), and that control is what the molecule conjecture asks, as the
hyperbolicity of the renormalization (Conjectures 3.5 and 3.6, Problem 3.1 of the survey). The
survey derives the hyperbolicity from the a priori bounds (Conjecture 3.6 needs Problem 4.3) and
the bounds from the hyperbolicity only a posteriori, so the hyperbolicity is available as a
hypothesis for a conditional route and cannot close the problems unconditionally.

What the structure gives that can be used now:

* **Tail invariance** (`Mlc/Research/TailInvariance.lean`, checked in Lean). In the abstract model
  of the towers, the Teichmüller contraction TC′, the cap G, the linear dichotomy D and the a
  priori bounds hold for a tower exactly when they hold for the tower without its first `n`
  levels (`lemmas_shift_iff`, `aPrioriBounds_shift_iff`); the constants change by quantities that
  the prefix determines. So the open classes are saturated under tuning by a bounded prefix, and
  it suffices to prove the lemmas for the tail. This is the grouping that the combinatorics
  supports: it removes bounded prefixes and removes nothing else, since the hard parameters have
  no bounded prefix to strip.
* **Metric similarity as the hypothesis to prove.** What a proof of Lemmas G and D must supply is
  the uniform comparison of the degeneration of `c` and of `τ_w(c)` with constants independent of
  `w` for relative periods of `w` that are unbounded (the pseudo-Siegel disks of PS1–PS4 are the
  survey's way to get it at the near-neutral steps).
* **Rays and fibers as the target form** (to formalize): rational parameter rays and their
  landing, fibers, and the equivalence "all fibers are points ⇒ locally connected", as an
  abstract topological theorem about a compact set with a family of separating pairs. It is
  independent of the dynamics, so it can be proved before the geometry and reduces the final
  statement of the tree to the triviality of fibers.

### The grid and the self-similarity of `M`

The kernel-checked grid and the structure above meet in one question: whether the many little
copies of `M` along the dendritic filaments can be covered in groups. The data of the grid say
how the cost grows. The unresolved cells counted at depth 9, 10, 11, 12 and 13 are 67 609,
224 189, 761 108, 2.42·10⁶ and 8.69·10⁶, a factor 3.2–3.6 per level (the count grows like
`h^{-1.77}` for cells of side `h`), while the certified bound of the unresolved area is 0.516,
0.428, 0.363, 0.289 and 0.259, a decrease of 12–17% per level. Every level costs a factor 3.4 in
kernel work and lowers the bound a little, and the exponent tends to 2 (the boundary of `M` has
Hausdorff dimension 2, Shishikura), so a hundredfold reduction by subdivision does not exist.
The unresolved layer is the neighbourhood of the part of `∂M` made of copies and their
filaments; each piece of `M` of the size of a cell must be surrounded by certified cells, and no
covering by squares is much cheaper.

A grouping by similarity needs more than the combinatorial similarity: the certificate of a
cell is arithmetic on its coordinates, and a model copy certifies a neighbour only with an
effective bound on the distortion of the tuning homeomorphism, the estimate of Problems 4.3 and
4.4 again (for Misiurewicz points, Tan Lei's asymptotic similarity with `J_c` has no effective
constants). What stays possible is cheaper certificates, not fewer cells: second-order Taylor
models certify larger squares at the same distance from `∂M`, and a covering of a copy by a disk
around its center needs an effective size estimate of the copy. Merging the modules does not
reduce the kernel work, which is the sum over the certificates, and the memory of a module grows with its work (2.4 GB for 13 seconds), so the modules cannot be
merged much; the build outputs shrink with `noncomputable` data (measured on a small tile: the
`.c` drops by 90% and the `.olean` by 42%, the fixed part of an `.olean` being 25 KB), which is a
matter of storage. The area is a by-product of the grid, and the grid stays at depth 13.

### Caveats

* The dictionary `Geometry` is a parameter of the statements: `cls`, `tower` and `vtower`
  are not defined from the dynamics of `f_c`. The theorem `mlc_of_programme` holds for every
  dictionary, so a faithful dictionary is what makes the lemmas statements about `M`.
* The widths of the towers are abstract positive numbers. `ExtremalLength.lean` defines an
  extremal width for families of length measures, and the towers are not yet built from it.
* The widths of the class of Problem 4.3 are pseudo-Siegel widths, a reading proposed here:
  the survey does not define them, and the lemmas TC′, G and D are statements about
  them.
* The classes are combinatorial, as the method requires: no class is defined by a
  local-connectivity conclusion.

## Route planning priors

The live graph and LaTeX report use the following broad planning ranges. They
are research-management priors:

| Route | Planned residual reduction | Success prior |
| --- | ---: | ---: |
| Problem 4.3 pseudo-Siegel control for remaining unbounded satellite cases | 10–30% | 12% |
| Problem 4.4 virtual bounded-period satellite interpolation | 24–46% | 20% |
| Problem 4.4 virtual near-neutral interpolation | 18–42% | 12% |
| Unified phase-parameter transfer conditional on genuine geometry | 38–72% | 45% |

The planned residual reduction is a relative research-management prior for the
residual set, the parameters that the published theorems leave open, and is
unrelated to the area of the grid or to the resolved share below. The final route is
conditional and cannot itself discharge Problems 4.3 and
4.4. Re-estimate each range only after a concrete class theorem, theorem-level
collar estimate, or parameter realization is added.

## Literature frontier

The source of the strategy is Dudko's
[MLC survey, §4–§4.5](https://arxiv.org/abs/2512.24171). The following search
terms define the next literature pass:

- `partially invariant virtual Julia sets`;
- `virtual Molecule renormalization`;
- `Dudko Kahn Lyubich virtual Julia`;
- `Elephant puzzles`;
- `Wave Lemma virtual Julia`;
- `virtual bounded-type satellite quasi-additivity`;
- `near-neutral phase parameter transfer`.

For each source, record the exact theorem, its hypotheses, the required
interfaces, and the boundary at which the source stops. The virtual-Julia
programme in §4.5 is a strategy; it does not supply the final global theorem.

## Quantitative progress metrics

Let `R` be the current residual parameter set:

```text
R = { c ∈ ∂M |
      c is not covered by the Problem 4.3 system and
      no VirtualMoleculeAPrioriControl is available at c }
```

Define the normalized outer-measure indicator

```text
q(R) = μ*(R) / (4π).
```

The trivial envelope is `q(R) ≤ 1`, because the Mandelbrot set is contained
in the closed disk of radius two. The current kernel-checked envelope comes from
the dyadic grid of `Mlc/GridCertified.lean`. A first-order model of the critical
orbit (center, derivative at the center, remainder) certifies a square as
outside `M` when the model leaves the disk of radius 2, and as inside `M` when a
moving disk centered at the model returns into itself, which gives a bounded
critical orbit for every parameter of the square. These squares are removed, and
the remaining cells in the upper half-plane (the lower half is the mirror image)
cover `M ∖ int M`. They are counted at side `2^-13`, 8694258 of them, which is
556432512 cells of side `2^-16`; the shells
of the hyperbolic components are certified by squares of side `2^-10` and `2^-11`
with inside certificates of up to 960 and 240 model steps (a coarse square costs
the kernel the same per unit of area as a cell of side `2^-12` with 60 steps):

```text
R ⊆ M ∖ int M
μ*(R) ≤ 2 · 556432512 / 4^16 ≈ 0.2591
q(R) ≤ 0.0206.
```

The resolved share is therefore at least `97.94%` of the disk envelope `|c| ≤ 2` (area
`4π`). The share is a by-product of the kernel-checked grid: the cells that no
certificate removes form a neighbourhood of `∂M` at the resolution of the grid, whose area
shrinks with the depth, and the share says nothing about the classes that the published
theorems leave open (the area of those parameters is unknown, expected to be small,
without a certificate). The report states no factor of reduction relative to the
literature. The earlier classifier with disk enclosures stopped at `11.2%`
(`q(R) ≤ 0.1117`): the disks lose the phases of the derivative, so squares at a
few cell widths from `M` stay unresolved, and a fixed trapping disk needs a
cell of side `s` to lie at distance about `√s` from the boundary of a
hyperbolic component, while the moving disk needs only a distance proportional
to `s`.

This bound holds for every candidate system and uses no unproved input. The
actual residual value remains unknown. A later
theorem covering class `C` must prove

```text
R_next = R \ C
μ*(R_next) ≤ μ*(R).
```

The next numerical gate is a resolved share of 99% (the gate of 95%,
`q(R) ≤ 0.05`, is reached):

```text
μ*(R) ≤ 4π / 100 = π / 25 ≈ 0.125664
q(R) ≤ 0.01.
```

Passing this gate requires a finer grid or a certified covering estimate of the
neighbourhood of `∂M`. No commit that
stages Lean sources is accepted unless it improves at least one of three
quantities and worsens none: the certified resolved share (the residual-area
envelope decreases), the share of parameter classes with a Lean certificate (the
proof of one statement of a class raises it by the statement's share of the class), and
the repository's formalization-debt proxy (it decreases when a milestone
theorem is added). The latter is

```text
2 / (1 + achieved milestone weight),
```

where the numerator is the two open root obligations and each denominator
milestone is a source symbol reachable from `MLC.mlc_conjecture`.

Area alone cannot certify MLC. A zero-area boundary is compatible with a
complicated fractal of locally disconnected components, so the metric must be
reported with:

- the supremum of unresolved parameter-piece radii;
- the number of unresolved first-return phases;
- the best proved lower separation budget;
- the covered class list;
- the number of open root declarations;
- the axiom frontier.

The Progress tab, the README and the status report show the **resolved share**
`100% − q(R)` as a number in a numbered table of the updates after the literature
baseline, each with its date and the result that raised it; the updates are stored in
the progress ledger (`docs/progress`), which survives squash merges. The baseline
(update 0) is the state of the literature: MLC follows from Dudko's Problems 4.3 and
4.4, which stay open. The area `4π` only normalizes the scale of the share, the area of
the parameters that the published theorems leave open is unknown (expected to be small,
without a certificate), and the baseline row lists the two open problems and claims no
unresolved area. A larger share is better, and it measures the grid; the progress on the
two problems is the number of open statements of the programme and the share of classes
with a Lean certificate, which the tab shows next to it.

### Reading the value 100%

`R` is the set of parameters of `M` without a proved local-connectivity
certificate, so `R = ∅` exactly when MLC is proved, and then `μ*(R) = 0`, i.e.
a resolved share of `100%`. The converse fails: a nonempty `R` of measure zero
also has `μ*(R) = 0`. The inclusion `R ⊆ ∂M` holds because local connectivity
is automatic at interior points, and the area of `∂M` is unknown, so a covering
argument alone cannot push the unresolved bound below that unknown value. MLC
is not known to decide the area of `∂M`, since a locally connected planar
continuum can have a boundary of positive area. Completion is therefore read
from the open root obligations and the existence of
`mlc_conjecture_unconditional`, never from the share alone.

### The area of `∂M`: route Z

The grid cannot reach `100%` without an input about `∂M`: the unresolved
cells at depth `d` cover a neighbourhood of `∂M` whose area decreases to
`area(∂M)`, and the measured ratio of one level to the next is `0.83–0.87`, so
every further level costs about three times more for a smaller gain. At depth 14
the search resolves 7% of the children of the unresolved cells of depth 13
(outside certificates of at most 32 steps), at about `3·10⁻¹⁰` of area per step
of the model, while depth 13 gave `1.1·10⁻⁹`; checking it would take about six
hours on 20 cores for a gain of `0.02`, that is `0.15%` of the share. Dudko's
survey states what is expected and what it needs:

- the introduction: "The area of `∂M` is expected to be 0, see §3.8";
- §3.8: Conjecture 3.6 (hyperbolicity of the Molecule renormalization), whose
  completion requires Problem 4.3, and which "is likely required for the
  satellite cases of Conjecture 1.2 and the Area Problem of `∂M`";
- §3, after the neutral renormalization: "Conjecturally, there is no
  renorm-expanding regime on the Molecule: every parameter there has
  substantial hyperbolic components in all scales";
- Question 3.1: at a scale `δ` of `c ∈ ∂M` there are three regimes, a
  Tan Lei similarity between `M` and `J_c` when all hyperbolic components are
  small relative to `δ`, near-neutral effects when a component of size `≫ δ`
  reaches the scale, and quadratic-like features when the components of size
  comparable to `δ` dominate.

A proof of area zero would make the unresolved bound `0` and the share `100%`
(MLC stays a separate statement). The proposed method, which the survey does not
state, reads the three regimes as a porosity statement and finishes with
Lebesgue's density theorem:

1. *Measure step (no dynamics).* If for every `c ∈ ∂M` there are `α > 0`,
   radii `r_n → 0` and points `y_n` with `B(y_n, α r_n) ⊆ B(c, r_n) ∖ ∂M`, then
   `area(∂M) = 0`. At a Lebesgue density point of `∂M` the proportion of
   `∂M` in `B(c, r_n)` tends to `1`, while the hole `B(y_n, α r_n)` removes the
   fixed proportion `α²`. This step is a Lean theorem on its own
   (`Mlc/Research/AreaZero.lean`): `volume_eq_zero_of_porous` for a measurable
   set that is porous at each of its points, from Mathlib's density theorem for
   doubling measures (`IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`),
   and `unresolved_volume_eq_zero_of_porous`, which states it for the unresolved
   set `M ∖ int M = ∂M`. Both use only the three kernel axioms.
2. *Geometric step.* The programme must supply the holes. In the Molecule regime
   they are the substantial hyperbolic components of every scale; in the
   quadratic-like regime they come from the a priori bounds (Problems 4.3 and
   4.4); in the renorm-expanding regime the almost-linear puzzle–parapuzzle
   relation transfers the porosity of `J_c` to `M`.
3. *Bookkeeping.* Route Z stays outside the root: `RootInput` keeps exactly
   Problems 4.3 and 4.4, and `unresolved_volume_eq_zero_of_porous` takes the
   porosity of step 2 as its hypothesis. The dependency graph treats it as a
   side result next to the root (`SIDE_ROOTS` in `scripts/spine_graph.py`).

The proof spine shows the chain Problem 4.3, Conjecture 3.6, area of `∂M` as
amber branches that are not formalized.

### Coverage-Uncertainty Profile

The **Coverage-Uncertainty Profile** is a dashboard invariant. Its components
record how much of the parameter space remains uncertain.

For a fixed parameter-class catalogue `Cᵢ`, class weights `wᵢ` with sum one,
and verified coverage `W`, define:

```text
A = μ*(R) / (4π)
C = Σᵢ wᵢ 1[Cᵢ is not covered]
K = Σᵢ wᵢ 1[Cᵢ is not covered] (h(dᵢ) + h(qᵢ)) / 2
B = Σᵢ wᵢ 1[Cᵢ is not covered] (1 - bᵢ)
U = (A + C + K + B) / 4.
```

Here `dᵢ` and `qᵢ` are fixed envelopes for return depth and relative period;
`bᵢ` is one only after a quantitative separation-budget certificate exists;
and `h(x) = x / (1 + x)`. An unknown quantity is conservatively scored as one.
Weights and the catalogue are frozen between progress baselines. A class
certificate then decreases `C` strictly by its weight, while every profile
component is nonincreasing.

`A` may already be zero on a null residual set while `C`, `K`, and `B` remain
positive. This is why the four-component profile is more informative than area
alone. Exact residual measure, infinite class complexity, and true future
research probability remain unknown.

## Ordered implementation milestones

1. Prove compactness of `M` and `M ⊆ closedBall 0 2` from first principles.
2. Formalize satellite-copy and relative-period combinatorics.
3. Formalize one restricted virtual bounded-period class end to end.
4. Construct its connected hull, restricted invariance, and first-return data.
5. Prove the corresponding collar and separation-budget estimate.
6. Construct the phase-parameter transfer and parameter nest.
7. Add the class to `CandidateSystem.Coverage`.
8. Repeat for the virtual near-neutral class.
9. Formalize the remaining unbounded satellite pseudo-Siegel branch.
10. Prove complete boundary coverage, instantiate `RootInput`, and discharge
    both open graph nodes.

Each milestone ends with a full `make check`, strict dependency-graph
generation, and the README audit.
