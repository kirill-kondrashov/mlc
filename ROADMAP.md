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

Line count is not a milestone. A successful cycle must replace a mathematical
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
are research-management priors, not mathematical probabilities:

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

The only unconditional envelope is `q(R) ≤ 1`, because the Mandelbrot set is
contained in the closed disk of radius two. The current checked envelope is

```text
μ*(R) ≤ 4π - π/16 = 63π/16
q(R) ≤ 63/64 = 0.984375.
```

The strict decrease comes from the proved inclusion
`ball(0,1/4) ⊆ interior M`. The actual residual value remains unknown. A later
theorem covering class `C` must prove

```text
R_next = R \ C
μ*(R_next) ≤ μ*(R).
```

The next numerical research gate is a verified 100-fold reduction of the
global envelope:

```text
μ*(R) ≤ 4π / 100 = π / 25 ≈ 0.125664
q(R) ≤ 0.01.
```

This target requires certified coverage of parameter classes, not a finer
sampling estimate. No commit is accepted as proof progress unless the certified
residual-area envelope and the repository's formalization-debt proxy both
strictly decrease. The latter is

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

README progress graphics should display the proven upper envelope and the
current `unknown` value. They must avoid a fabricated decreasing area curve.

### Coverage-Uncertainty Profile

The name **Coverage-Uncertainty Profile** is preferred to entropy. It is a
dashboard invariant, inspired by entropy-style bookkeeping, but it is not a
thermodynamic or information-theoretic entropy.

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
