## Executive finding

The proposed `ParaPieceCarvedByMotion` route is **internally inconsistent in the straddling case** as currently defined. The core issue is genuine: `ParaPieceCarvedByMotion c n` asks for a time-slice `H.f t` of a `SpaceHolomorphicMotion` on
`S(c,n) := {c' | green_function c (c' - c) < (1/2 : ℝ)^n}`
whose image is exactly `S(c,n) ∩ MandelbrotSet`.

But for any such slice:
- `SpaceHolomorphicMotion` gives `DifferentiableOn ℂ (H.f t) U` on an **open** set `U` with `S(c,n) ⊆ U`;
- `HolomorphicMotion.h_inj` gives `InjOn (H.f t) S(c,n)` for `t ∈ ball 0 1`;
- `S(c,n)` is nonempty and open, and in the straddling case contains both a Mandelbrot point (`c`) and a non-Mandelbrot point;
- thus `H.f t` cannot be locally constant everywhere on `S(c,n)` (otherwise injectivity on an open nonempty set would fail), so by the complex open mapping theorem it sends every open subset of `S(c,n)` to an open set.

Hence `H.f t '' S(c,n)` must be open. But in the straddling case `S(c,n) ∩ MandelbrotSet` is **not open**. Therefore `ParaPieceCarvedByMotion c n` is impossible in that case.

So the carving reduction in `Mlc/ParaPuzzleCarvingReduction.lean` is too strong to serve as a realizable route for the frontier axiom on straddling pieces. The correct replacement must weaken the image requirement, e.g. to a motion of a connected reference set that is **not itself open**, or to a correspondence/quotient/gluing statement rather than an injective holomorphic self-map of the open translate.

## Corrections to the suspected argument

1. **`S(c,n)` open / connected / contains `c`: corrected to “open and connected are confirmed; `c ∈ S(c,n)` follows from an existing Green-zero lemma, not from the carving file itself.”**
   - Openness of strict Green sublevels is standard from continuity; a direct repo proof exists for Green sublevels and `ParaPuzzlePieceAt`, and the same pattern applies to `S(c,n)`.
   - Connectivity of `S(c,n)` is already proved as `green_sublevel_translate_connected`.
   - Membership `c ∈ S(c,n)` follows because `green_function c (c - c) = green_function c 0 = 0 < (1/2)^n`, using `Quadratic.green_sublevel_contains_0` after transport through translation.

2. **`SpaceHolomorphicMotion` holomorphy domain:** confirmed to be on a larger set `U`, not merely on `S`.
   - `SpaceHolomorphicMotion` has fields:
     - `U : Set ℂ`
     - `hEU : E ⊆ U`
     - `hU_open : IsOpen U`
     - `h_space_holo : ∀ t ∈ ball 0 1, DifferentiableOn ℂ (f t) U`
   - So the open-mapping input is stronger than suspected: the slice is holomorphic on an **open neighborhood-domain** containing `S`.

3. **Need for nonconstancy:** injectivity on `S` is enough, but only locally after restricting to a small ball inside `S`.
   - Open mapping in Mathlib is phrased as `AnalyticOnNhd.is_constant_or_isOpen` on a preconnected set `U`.
   - Since `S(c,n)` is open, every point `z ∈ S(c,n)` has a small ball `B ⊆ S(c,n)`.
   - If `H.f t` were constant on `B`, injectivity on `S(c,n)` would fail because `B` has at least two points.
   - Therefore on each such ball, the slice is nonconstant, hence open there; this yields openness of the image globally as a union of open images of small balls.
   - So the mathematically precise route is **local**, not a one-shot global application to `S(c,n)`.

4. **`S(c,n) ∩ MandelbrotSet` non-open in the straddling case:** correct, but one should prove it from a frontier point produced from openness/closedness, not merely assert it.
   - Inputs:
     - `c ∈ MandelbrotSet` and `c ∈ S(c,n)`;
     - `¬ S(c,n) ⊆ MandelbrotSet`, so choose `x ∈ S(c,n) \ MandelbrotSet`;
     - `S(c,n)` is connected;
     - `MandelbrotSet` is closed.
   - If `S(c,n) ∩ MandelbrotSet` were open in `S(c,n)`, then it would also be closed in `S(c,n)` because it is `S(c,n) ∩ MandelbrotSet` with `MandelbrotSet` closed in `ℂ`.
   - It is nonempty (contains `c`) and proper (misses `x`), contradicting preconnectedness/connectedness of `S(c,n)`.
   - This is cleaner than constructing an explicit point in `S ∩ frontier MandelbrotSet`, though one can derive such a point afterward.

5. **Frontier-point construction:** it can be obtained cleanly if desired.
   - From nonempty proper clopen contradiction, one gets that `S ∩ M` is not open in the subspace `S`.
   - Equivalently, there exists `y ∈ S ∩ M` such that every neighborhood of `y` in `S` meets `S \ M`; since `S` is open in `ℂ`, this gives `y ∈ frontier MandelbrotSet` and `y ∈ S`.
   - But for the no-go theorem, explicit frontier-point extraction is unnecessary.

6. **Conclusion:** the no-go theorem should target `ParaPieceCarvedByMotion`, not the weaker `ParaPieceIsMotionImage`.
   - `ParaPieceIsMotionImage` only asks for a connected reference set `E`; if `E` is not open, open mapping does not force `H.f t '' E` open.
   - The obstruction is specifically to **holomorphic self-carving of an open set by an injective slice**.

## Declarations inspected

### Repository declarations

1. `Mlc/ParaPuzzleCarvingReduction.lean`
   - `ParaPieceCarvedByMotion` (lines 24–30):
     ```lean
     def ParaPieceCarvedByMotion (c : ℂ) (n : ℕ) : Prop :=
       ∃ (H : Quadratic.SpaceHolomorphicMotion
               {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}) (t : ℂ),
         t ∈ Metric.ball (0 : ℂ) 1 ∧
           H.f t '' {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n}
             = {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ∩ MandelbrotSet
     ```
   - `isConnected_greenSublevel_inter_mandelbrot_of_carvedByMotion` (lines 41–48).

2. `Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean`
   - `structure SpaceHolomorphicMotion` (lines 47–58): open holomorphy domain `U`, inclusion `hEU`, openness `hU_open`, slice holomorphy `h_space_holo`.
   - `SpaceHolomorphicMotion.isConnected_image` (lines 76–80).
   - `ParaPieceIsMotionImage` (lines 91–95): weaker motion-image hypothesis.

3. `Mlc/ParaPuzzleConnectivity.lean`
   - `green_sublevel_translate_connected` (lines 128–145): confirms connectedness of `S(c,n)` for `c ∈ MandelbrotSet`.
   - `green_sublevel_translate_inter_mandelbrot_connected_of_subset` (lines 153–160).
   - `green_sublevel_translate_inter_mandelbrot_connected_straddling` (lines 207–211): exact frontier axiom.
   - `green_sublevel_translate_inter_mandelbrot_connected` (lines 216–223): case split theorem reducing to the straddling axiom.

4. `Mlc/Quadratic/Complex/ParaPuzzleBasis.lean`
   - `isOpen_compl_mandelbrotSet`.
   - `isClosed_mandelbrotSet`.
   - `para_puzzle_piece_at_isOpen`.

5. `Mlc/LcAtOfShrink.lean`
   - `LocallyConnectedAt` definition.
   - `lc_at_of_shrink_of_data`.

6. `Mlc/InfinitelyRenormalizable.lean`
   - `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`.
   - `mlc_finitely_renormalizable`.

7. `Mlc/AxiomsMainConjecture.lean`
   - `parameter_shrink_of_yoccoz`.

8. `Mlc/MainConjecture.lean`
   - `mlc_strategy_of_branchLocalData`.

### Mathlib declarations

1. `Mathlib/Analysis/Complex/OpenMapping.lean`
   - `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`
   - `AnalyticOnNhd.is_constant_or_isOpen`

2. `Mathlib/Topology/Connected/LocPathConnected.lean`
   - `IsOpen.isConnected_iff_isPathConnected`
   - local-path-connected facts via open subsets.

## Confirmed Mathlib APIs

All signatures below were confirmed from source, not memory.

1. **Open mapping theorem**
   - File/import: `Mathlib.Analysis.Complex.OpenMapping`
   - Confirmed theorem:
     ```lean
     theorem AnalyticOnNhd.is_constant_or_isOpen
       (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) :
       (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s)
     ```
   - Use: on a small ball `B ⊆ S(c,n)` where slice holomorphy holds; injectivity rules out the constant branch.

2. **Local open mapping form**
   - File/import: `Mathlib.Analysis.Complex.OpenMapping`
   - Confirmed theorem:
     ```lean
     theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds
       {z₀ : E} (hg : AnalyticAt ℂ g z₀) :
       (∀ᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) ≤ map g (𝓝 z₀)
     ```
   - Use: alternative pointwise proof that each image point has neighborhood inside `H.f t '' S`.

3. **Connected open subsets are path connected in locally path connected spaces**
   - File/import: `Mathlib.Topology.Connected.LocPathConnected`
   - Confirmed theorem:
     ```lean
     theorem IsOpen.isConnected_iff_isPathConnected {U : Set X} (U_op : IsOpen U) :
       IsConnected U ↔ IsPathConnected U
     ```
   - This is available if a path-connected route is desired. For `ℂ`, local path connectedness is standard via normed-space instances.

4. **Openness of strict sublevel preimages**
   - Generic API, confirmed used in repo:
     - `isOpen_lt` used in `Mlc/GreenSublevelConnectedDirect.lean`
     - also `IsOpen.preimage ... isOpen_Iio` appears in repo.
   - For the target set one can use either:
     ```lean
     isOpen_lt ((continuous_green_function c).comp (continuous_id.sub continuous_const)) continuous_const
     ```
     or
     ```lean
     IsOpen.preimage ((continuous_green_function c).comp (continuous_id.sub continuous_const)) isOpen_Iio
     ```
   - Import exposure in repo context: continuity theorem comes from project files; the generic topological API is Mathlib core/topology.

5. **Open sets via neighborhoods**
   - File/import: `Mathlib.Topology.Neighborhoods`
   - Confirmed theorem:
     ```lean
     theorem isOpen_iff_mem_nhds : IsOpen s ↔ ∀ x ∈ s, s ∈ 𝓝 x
     ```
   - Useful for the “not open” contradiction or local image-openness packaging.

6. **Connectedness vs clopen decomposition**
   - Confirmed available indirectly through `IsPreconnected` APIs in Mathlib’s connected/clopen files; enough to prove that a nonempty proper subset of connected `S` cannot be both open-in-`S` and closed-in-`S`.
   - The exact theorem best suited was not isolated to a single named lemma during this audit; see “Unconfirmed or missing APIs”.

## Unconfirmed or missing APIs

1. **A single exact theorem name for “strict-sublevel preimage is open” specialized to the target set `S(c,n)`**
   - Generic APIs are confirmed (`isOpen_lt`, `IsOpen.preimage ... isOpen_Iio`), but I did not isolate one project declaration already naming `IsOpen S(c,n)`.

2. **A single exact theorem name for “open connected subset containing a point of a closed set and a point outside it gives non-open intersection”**
   - This appears not to exist as a ready-made Mathlib lemma in the exact form needed.
   - Likely easiest proof is short and direct using connectedness + relative clopen contradiction.

3. **A one-line theorem for “injective on a nonempty open ball implies nonconstant on that ball”**
   - No dedicated theorem was located; trivial to prove ad hoc.

4. **A one-line theorem for “subspace-open plus ambient-closed gives clopen in the subspace”**
   - Standard via `IsOpen.preimage` / induced topology, but no exact packaged theorem name was isolated.

## Proposed Lean theorem signatures

### 1. General no-go lemma (preferred)

```lean
theorem image_not_mandelbrot_inter_of_open_holo_inj
    {S U : Set ℂ} {f : ℂ → ℂ}
    (hS_open : IsOpen S)
    (hS_conn : IsConnected S)
    (hS_nonempty : S.Nonempty)
    (hSU : S ⊆ U)
    (hU_open : IsOpen U)
    (hf_holo : DifferentiableOn ℂ f U)
    (hf_inj : Set.InjOn f S)
    (hM_closed : IsClosed MandelbrotSet)
    (hSinM : ∃ z ∈ S, z ∈ MandelbrotSet)
    (hSoutM : ∃ z ∈ S, z ∉ MandelbrotSet) :
    f '' S ≠ S ∩ MandelbrotSet
```

Why these hypotheses:
- `hS_open`, `hSU`, `hU_open`, `hf_holo`: to get local analyticity/open mapping on balls inside `S`.
- `hS_conn`: to show `S ∩ MandelbrotSet` cannot be open when it is also closed, nonempty, and proper.
- `hf_inj`: to exclude local constancy on each ball.
- `hSinM`, `hSoutM`: to make `S ∩ MandelbrotSet` nonempty and proper.
- `hM_closed`: to make `S ∩ MandelbrotSet` closed in `S`.

Proof sketch:
1. Show `IsOpen (f '' S)` by covering `S` by balls `B ⊆ S`, applying `AnalyticOnNhd.is_constant_or_isOpen` on each `B`, and using `hf_inj` to rule out constant-on-`B`.
2. Show `¬ IsOpen (S ∩ MandelbrotSet)` from connectedness of `S`: if open, it is also closed in `S`, nonempty, and proper.
3. Conclude inequality.

### 2. Specialization to the carving hypothesis

```lean
theorem not_paraPieceCarvedByMotion_of_straddling
    {c : ℂ} (hc : c ∈ MandelbrotSet) (n : ℕ)
    (hstraddle : ¬ {c' | green_function c (c' - c) < (1 / 2 : ℝ) ^ n} ⊆ MandelbrotSet) :
    ¬ ParaPieceCarvedByMotion c n
```

Why sufficient:
- This directly kills the proposed route exactly where the frontier axiom lives.
- `S`-connectedness comes from `green_sublevel_translate_connected hc n`.
- `c ∈ S` comes from `green_function c 0 = 0` / `green_sublevel_contains_0` transported by translation.
- `∃ x ∈ S, x ∉ M` comes by unpacking `hstraddle`.
- `IsClosed MandelbrotSet` is `isClosed_mandelbrotSet`.
- Holomorphy/injectivity/open-domain fields come from unpacking the witness `H : SpaceHolomorphicMotion S`.

### 3. Useful intermediate theorem

```lean
theorem SpaceHolomorphicMotion.isOpen_image_of_isOpen
    {E : Set ℂ} (H : SpaceHolomorphicMotion E) {t : ℂ}
    (ht : t ∈ Metric.ball (0 : ℂ) 1) :
    IsOpen E → IsOpen (H.f t '' E)
```

This would be broadly reusable, but only after proving the local nonconstancy/open-mapping argument from `H.h_inj` and `H.h_space_holo`.

### 4. Topological helper

```lean
theorem inter_closed_not_open_of_connected_of_nontrivial
    {S M : Set ℂ}
    (hS_conn : IsConnected S)
    (hM_closed : IsClosed M)
    (h_in : ∃ z ∈ S, z ∈ M)
    (h_out : ∃ z ∈ S, z ∉ M) :
    ¬ IsOpen (S ∩ M)
```

This is the cleanest reusable topological payload for the contradiction.

## Dependency trace toward MLC

### Facts proved by the code

1. **Parameter-piece connectedness hook implies local connectivity at a point**
   - `Mlc/LcAtOfShrink.lean`
   - `lc_at_of_shrink_of_data`:
     from `ParaPuzzlePieceInterMandelbrotConnectedData` + shrinkage
     `⋂ n, ParaPuzzlePieceAt c n = {c}`
     deduces `LocallyConnectedAt MandelbrotSet ⟨c,hc⟩`.

2. **Finitely renormalizable endpoint from connectedness hook**
   - `Mlc/InfinitelyRenormalizable.lean`
   - `mlc_finitely_renormalizable_of_paraPuzzleConnectedData`.

3. **Axiom-backed finitely-renormalizable wrapper**
   - `Mlc/InfinitelyRenormalizable.lean`
   - `mlc_finitely_renormalizable` routes through
     `Quadratic.para_puzzle_transport_exists_data_of_motion_default`.

4. **Parameter shrinkage bridge from Yoccoz shrinkage input**
   - `Mlc/AxiomsMainConjecture.lean`
   - `parameter_shrink_of_yoccoz`:
     from dynamical shrinkage `(⋂ n, DynamicalPuzzlePiece c n 0) = {0}`
     to parameter shrinkage `(⋂ n, ParaPuzzlePieceAt c n) = {c}`.

5. **Global MLC strategy assembly**
   - `Mlc/MainConjecture.lean`
   - `mlc_strategy_of_branchLocalData`:
     if one has local connectivity on the finite side and the infinite-side classification/bridge, then
     `LocallyConnectedSpace MandelbrotSet`.

### Mathematical inferences from the architecture

1. The repository treats the connectivity statement
   `IsConnected (ParaPuzzlePieceAt c n ∩ MandelbrotSet)`
   as a key bridge from puzzle geometry to local connectivity (`LcAtOfShrink`).

2. Thus the straddling frontier axiom in `ParaPuzzleConnectivity.lean` is not just cosmetic: it feeds the finite-renormalizable local-connectivity route through the connectedness hook.

3. However, the code does **not** prove that this universal connectivity target is “merely” Yoccoz’s finitely-renormalizable theorem in any repository-internal theorem equivalence sense. What it does prove is a dependency chain:
   connectivity hook + shrinkage ⇒ `LocallyConnectedAt`; and finite-renormalizable + shrinkage ⇒ local connectivity.

### Literature claims not verified from repository contents

1. The docstring claim that the straddling axiom is “Yoccoz's theorem for finitely renormalizable parameters” is a mathematical interpretation, not a repository-proved equivalence.
2. Any claim that the universal connectivity target is exactly the classical finitely-renormalizable Yoccoz theorem, with no extra hypotheses or reformulation gap, needs a later sourced literature audit.
3. The repository imports `Yoccoz.Yoccoz`, but this audit did not inspect external package semantics deeply enough to certify exact literature alignment.

## Blockers

### mathematical
- `ParaPieceCarvedByMotion` is obstructed by open mapping in the straddling case.
- Therefore that route cannot discharge the frontier axiom as stated.

### missing repository definitions
- No existing repository theorem packages the no-go argument.
- No pre-existing declaration explicitly states `IsOpen S(c,n)` for the translated sublevel set, though it is easy from continuity.

### Mathlib/API
- No single ready-made theorem was located for the full “connected open set + closed ambient set + inside/outside points ⇒ intersection not open” pattern.
- The proof will need a small custom topological lemma.

### proof engineering
- The clean proof should use local balls inside `S(c,n)` and `AnalyticOnNhd.is_constant_or_isOpen`, rather than trying to force a single global open-mapping invocation.
- Care is needed to phrase openness of `S ∩ MandelbrotSet` either in ambient `ℂ` or relative to `S`; relative openness is the natural contradiction target.

## Commands and verification

Commands used during the audit:

```bash
view plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
view Mlc/ParaPuzzleCarvingReduction.lean
view Mlc/ParaPuzzleConnectivity.lean
view Mlc/Quadratic/Complex/Bottcher/Slodkowski.lean
view Mlc/Quadratic/Complex/ParaPuzzleBasis.lean
view Mlc/Quadratic/Complex/Axioms.lean
view Mlc/LcAtOfShrink.lean
view Mlc/InfinitelyRenormalizable.lean
view Mlc/MainConjecture.lean
view .lake/packages/mathlib/Mathlib/Analysis/Complex/OpenMapping.lean
view .lake/packages/mathlib/Mathlib/Topology/Connected/LocPathConnected.lean
grep ... relevant declarations and Mathlib APIs ...
git status --short
```

`git status --short` at completion:

```text
?? plan/GPT54_RESULT_01_PARAMETER_CONNECTIVITY_AUDIT.md
?? plan/GPT54_TASK_01_PARAMETER_CONNECTIVITY_AUDIT.md
```

## Change-safety confirmation

- no Lean source was edited;
- no existing plan or documentation file was edited;
- the result file is the only repository change made by this task;
- no `axiom`, `sorry`, `admit`, or equivalent target-strength hypothesis was introduced;
- no commit was created.
