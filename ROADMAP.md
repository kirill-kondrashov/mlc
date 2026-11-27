# MLC research roadmap

## Goal and current invariant

The target is an unconditional theorem

```lean
LocallyConnectedSpace MLC.mandelbrotSet
```

with an axiom frontier limited to Lean's standard foundations. The active proof
must retain the invariant that every declaration is connected to
`MLC.mlc_conjecture`. The graph currently exposes two open mathematical
inputs: Problem 4.3 and Problem 4.4.

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

## Class hierarchy

The final coverage argument should organize every `c ∈ M` into disjoint or
prioritized classes:

| Class | Expected route | Status |
| --- | --- | --- |
| Hyperbolic/interior parameters | Convex subspace neighborhoods | Handled by the topological kernel |
| Non-renormalizable and positive-core-entropy parameters | Primitive pull-off and principal/puzzle expansion | Published literature; substantial Lean work remains |
| Bounded-type primitive and satellite ql parameters | Uniform ql bounds plus parapuzzle shrinkage | Published literature; substantial Lean work remains |
| Anti-Molecule primitive parameters | Puzzle levels and phase-parameter transfer | Published literature; substantial Lean work remains |
| Remaining unbounded satellite ql parameters | Pseudo-Siegel a priori bounds | Problem 4.3 |
| Virtual bounded-period satellite chains | Virtual-Molecule width amplification | Problem 4.4 |
| Virtual near-neutral chains | Pseudo-Siegel regularization and interpolation | Problem 4.4 |
| Exceptional unclassified boundary points | Contradiction or an explicit singleton/control theorem | Must be empty at completion |

Every class definition must use dynamical data such as first-return type,
relative period, renormalization phase, or geometric control. A class may not
be defined by the local-connectivity conclusion itself.

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

## Route planning priors

The live graph and LaTeX report use the following broad planning ranges. They
are research-management priors:

| Route | Expected relative residual reduction | Success prior |
| --- | ---: | ---: |
| Problem 4.3 pseudo-Siegel control for remaining unbounded satellite cases | 10–30% | 12% |
| Problem 4.4 virtual bounded-period satellite interpolation | 24–46% | 20% |
| Problem 4.4 virtual near-neutral interpolation | 18–42% | 12% |
| Unified phase-parameter transfer conditional on genuine geometry | 38–72% | 45% |

The final route is conditional and cannot itself discharge Problems 4.3 and
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

The resolved share is therefore at least `97.94%`, a 48-fold reduction of the
unresolved area. The earlier classifier with disk enclosures stopped at `11.2%`
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

The next numerical research gate is a verified 100-fold reduction of the
global envelope (the 20-fold gate `q(R) ≤ 0.05` is reached):

```text
μ*(R) ≤ 4π / 100 = π / 25 ≈ 0.125664
q(R) ≤ 0.01.
```

This target requires certified coverage of parameter classes. No commit is
accepted as proof progress unless the certified
resolved share strictly increases (the residual-area envelope strictly
decreases) and the repository's formalization-debt proxy does not increase.
The latter is

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
`100% − q(R)` as a number in a table of the commits after the literature
baseline, each with the result that raised it. The baseline is the first commit
whose formal root is exactly Dudko's Problems 4.3 and 4.4; its row lists the two
open problems, and a larger share is better.

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
