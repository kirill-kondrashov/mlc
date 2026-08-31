# GPT-5.4 Result 27: parameter external coordinate feasibility

## Verdict

**Decision: 1. coordinate and outside-disk theorem are ready to implement.**

The repository already contains an **axiom-clean** candidate for
`Φ_M(c) = B_c(c)` on `c ∉ MandelbrotSet`: namely

```lean
Quadratic.proxy_bottcher_map c c
```

with

```lean
Quadratic.proxy_bottcher_map c z = Quadratic.polar_green_map c z
```

and the domain bridge plus outside-disk theorem compile from existing checked lemmas.

## A. Candidate inventory and dependency audit

### Preferred axiom-clean candidate

1. `Mlc/Quadratic/Complex/Bottcher/BottcherCore.lean`

```lean
noncomputable def polar_green_map (c : ℂ) (z : ℂ) : ℂ := ...
noncomputable def proxy_bottcher_map (c : ℂ) (z : ℂ) : ℂ := polar_green_map c z
```

Mathematical shape:
- total function `ℂ → ℂ → ℂ`;
- normalization by modulus:
  `‖proxy_bottcher_map c z‖ = exp (green_function c z)`;
- intended dynamical domain is the basin, but the definition itself is total.

Key checked theorem:

```lean
theorem norm_bottcher_eq_exp_green (c : ℂ) (z : ℂ) :
    ‖proxy_bottcher_map c z‖ = Real.exp (MLC.Quadratic.green_function c z)
```

Dependency status:
- definition is explicit, not an axiom;
- no `sorry`/`admit` in the declaration path used here;
- usable without `BottcherOnM` hypothesis bundles.

2. `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`

```lean
lemma one_lt_norm_polar_green_map_of_mem_basin (c z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    1 < ‖polar_green_map c z‖
```

This is the exact outside-unit-disk theorem needed once evaluation at `z = c` is justified.

### Constructive but not directly the parameter coordinate

3. `BottcherInverse.lean`

- `recipBottcher_exists_analytic_inverse`
- genuine local analytic inverse near infinity, fiberwise in `w`.

4. `BottcherParamHolo.lean`

- `logSeriesBottcherApprox_differentiableOn_param`
- parameter holomorphicity of the near-infinity Böttcher approximant.

5. `BottcherParamInverse.lean`

- `exists_param_holo_bottcher_inverse`
- c-holomorphic inverse near infinity for the joint near-infinity family.

These are genuine and axiom-clean, but they do **not** by themselves define the parameter-plane map
`c ↦ B_c(c)` on `ℂ \ MandelbrotSet`.

### Rejected candidate routes

6. `BottcherAxioms.lean`

Contains axiom-backed/global placeholder material such as:
- `external_ray_map_exists`
- `bottcher_seq_converges`
- `extended_ray_map_continuous`
- `extended_ray_map_free_continuous`

7. `BottcherOnMTheory.lean`

Still contains axiom/hypothesis-frontier material including:
- `bottcher_outside_axiom`
- `proxy_bottcher_map_inj_on_K`

So these files are **not** the foundation for Task 27. The honest usable basis is the explicit proxy
`proxy_bottcher_map = polar_green_map` together with basin/K/Green lemmas.

## B. Domain bridge from `c ∉ MandelbrotSet`

The bridge is available and compile-checks.

### Repository definitions used

From `Yoccoz/Quadratic/Complex/Basic.lean`:

```lean
def K (c : ℂ) : Set ℂ := { z | boundedOrbit c z }
def MandelbrotSet : Set ℂ := { c | boundedOrbit c 0 }
```

So:
- `c ∈ MandelbrotSet` means `boundedOrbit c 0`;
- `c ∈ K c` means `boundedOrbit c c`.

### Orbit-shift fact

From `Mlc/ParaPuzzleContainment.lean`:

```lean
lemma orbit_param_eq_orbit_zero_succ (c : ℂ) (n : ℕ) :
    orbit c c n = orbit c 0 (n + 1)
```

This is the exact orbit-tail identity relating the critical value orbit to the critical orbit.

### Basin/K bridge

From `Mlc/Quadratic/Complex/Bottcher/BottcherCore.lean`:

```lean
theorem basin_eq_compl_K (c : ℂ) : basin_of_infinity c = (MLC.Quadratic.K c)ᶜ
```

From `Mlc/GreenSublevelJoinedToKc.lean`:

```lean
lemma z_in_basin_of_not_mem_K (c : ℂ) (z : ℂ) (h : z ∉ MLC.Quadratic.K c) :
    z ∈ Quadratic.basin_of_infinity c
```

### Outside-disk theorem on the basin

From `ConstructiveBasinCoordinate.lean`:

```lean
lemma one_lt_norm_polar_green_map_of_mem_basin (c z : ℂ)
    (hz : z ∈ basin_of_infinity c) :
    1 < ‖polar_green_map c z‖
```

### Compiled Lean proof

I compiled the following in `/tmp/task27_probe.lean` with:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task27_probe.lean
```

Code:

```lean
import Mlc.ParaPuzzleContainment
import Mlc.GreenSublevelJoinedToKc
import Mlc.Quadratic.Complex.Bottcher.ConstructiveBasinCoordinate

open MLC Quadratic Complex Set Filter Metric Real

namespace Task27Probe

noncomputable def parameterExternalCoord (c : {c : ℂ // c ∉ MandelbrotSet}) : ℂ :=
  Quadratic.proxy_bottcher_map c.1 c.1

lemma critical_value_not_mem_K (c : {c : ℂ // c ∉ MandelbrotSet}) :
    c.1 ∉ Quadratic.K c.1 := by
  intro hcK
  have hbd : MLC.Quadratic.boundedOrbit c.1 c.1 := by
    change MLC.Quadratic.boundedOrbit c.1 c.1 at hcK
    exact hcK
  obtain ⟨B, hB⟩ := hbd
  have hM : c.1 ∈ MandelbrotSet := by
    refine ⟨max B ‖c.1‖, ?_⟩
    intro n
    cases' n with n
    · simpa using (le_max_right B ‖c.1‖)
    · have hstep : orbit c.1 0 (n + 1) = orbit c.1 c.1 n := by
        rw [← MLC.Quadratic.orbit_param_eq_orbit_zero_succ c.1 n]
      rw [hstep]
      exact le_trans (hB n) (le_max_left B ‖c.1‖)
  exact c.2 hM

lemma critical_value_in_basin (c : {c : ℂ // c ∉ MandelbrotSet}) :
    c.1 ∈ Quadratic.basin_of_infinity c.1 :=
  z_in_basin_of_not_mem_K c.1 c.1 (critical_value_not_mem_K c)

lemma one_lt_norm_parameterExternalCoord (c : {c : ℂ // c ∉ MandelbrotSet}) :
    1 < ‖parameterExternalCoord c‖ := by
  have hbasin : c.1 ∈ Quadratic.basin_of_infinity c.1 := critical_value_in_basin c
  simpa [parameterExternalCoord, Quadratic.proxy_bottcher_map]
    using Quadratic.one_lt_norm_polar_green_map_of_mem_basin c.1 c.1 hbasin

end Task27Probe
```

Outcome:
- compiled successfully;
- only warning was an unnecessary `simpa` linter suggestion.

### Conclusion of the bridge

From existing checked lemmas:
1. `c ∉ MandelbrotSet` means `¬ boundedOrbit c 0`.
2. If `c ∈ K c`, then the orbit-shift lemma yields `c ∈ MandelbrotSet`.
3. Hence `c ∉ K c`.
4. Therefore `c ∈ basin_of_infinity c`.
5. Therefore `1 < ‖proxy_bottcher_map c c‖`.

So Task 27 is **not blocked** at the domain step.

## C. Definition shape

Three options:

1. **Subtype-valued target**

```lean
def parameterExternalCoord :
  {c : ℂ // c ∉ MandelbrotSet} → {w : ℂ // 1 < ‖w‖}
```

Pros: codomain carries the outside-disk fact.
Cons: heavier API and more coercion noise.

2. **Unbundled complex-valued definition + theorem**

```lean
def parameterExternalCoord (c : {c : ℂ // c ∉ MandelbrotSet}) : ℂ :=
  Quadratic.proxy_bottcher_map c.1 c.1

theorem one_lt_norm_parameterExternalCoord ...
```

Pros: smallest honest API; compile-tested; enough for later rays/equipotentials once one chooses bundling wrappers.
Cons: target-side property not bundled.

3. **Partial/total function on all `ℂ`**

Not recommended. The natural domain is already the subtype `c ∉ MandelbrotSet`, and a total extension would add arbitrary behavior on `M`.

### Recommendation

Use **option 2** now:
- minimal;
- honest;
- already compile-tested;
- does not overcommit to a final codomain packaging.

A subtype-valued wrapper can be added later immediately on top of the theorem.

## D. Holomorphicity and conformality boundary

### Already enough for definition

For Task 27, only these are required:
- a coordinate candidate `B_c(z)`;
- evaluation at `z = c` for `c ∉ M`;
- proof `1 < ‖B_c(c)‖`.

These are available axiom-clean via the compiled probe.

### Not yet established by this audit

This audit did **not** find a checked parameter-plane package proving all of:
- continuity of `c ↦ B_c(c)` on `ℂ \ M`;
- holomorphicity on `ℂ \ M`;
- tangent-to-identity asymptotics at parameter infinity;
- injectivity/surjectivity as a conformal equivalence `ℂ \ M ≃ ℂ \ closedDisk`.

The repo does contain strong near-infinity and inverse-family results (`BottcherParamHolo`,
`BottcherInverse`, `BottcherParamInverse`), but they are still about the joint/fiber Böttcher family,
not yet the full parameter-plane uniformization theorem.

So the correct boundary is:
- **definition + outside-disk theorem:** ready now;
- **global conformality package:** later frontier.

## E. First implementation milestone

The first honest milestone is exactly:

```lean
noncomputable def parameterExternalCoord
    (c : {c : ℂ // c ∉ MandelbrotSet}) : ℂ :=
  Quadratic.proxy_bottcher_map c.1 c.1

lemma critical_value_in_basin
    (c : {c : ℂ // c ∉ MandelbrotSet}) :
    c.1 ∈ Quadratic.basin_of_infinity c.1 := ...

theorem one_lt_norm_parameterExternalCoord
    (c : {c : ℂ // c ∉ MandelbrotSet}) :
    1 < ‖parameterExternalCoord c‖ := ...
```

No axiom bundle is needed for this milestone.

## Exact next worker task

Implement the minimal parameter external coordinate layer in Lean:
- define `parameterExternalCoord (c : {c // c ∉ MandelbrotSet}) := Quadratic.proxy_bottcher_map c.1 c.1`;
- add `critical_value_in_basin` and `one_lt_norm_parameterExternalCoord`;
- prefer the unbundled `ℂ`-valued API plus theorem;
- do **not** yet claim continuity, holomorphicity, injectivity, surjectivity, or conformal equivalence.

## Searches and commands used

Searches/read audit included:
- `grep` over `Mlc/` for `MandelbrotSet`, `basin_eq_compl_K`, `z_in_basin_of_not_mem_K`,
  `green_function_pos_of_basin`, and coordinate candidates;
- inspected:
  - `Mlc/Quadratic/Complex/Bottcher/BottcherCore.lean`
  - `Mlc/Quadratic/Complex/Bottcher/ConstructiveBasinCoordinate.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherAxioms.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherOnMTheory.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherParamHolo.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherParamInverse.lean`
  - `Mlc/Quadratic/Complex/Bottcher/BottcherInverse.lean`
  - `Mlc/ParaPuzzleContainment.lean`
  - `Mlc/GreenSublevelJoinedToKc.lean`
  - `.lake/packages/yoccoz-theorem/Yoccoz/Quadratic/Complex/Basic.lean`

Compile probe command:

```bash
cd /home/kir/pers/mlc && lake env lean /tmp/task27_probe.lean
```

Final outcome: success.

## Status / write confirmation

- Wrote only this result artifact:
  `plan/GPT54_RESULT_27_PARAMETER_EXTERNAL_COORDINATE_FEASIBILITY.md`
- No Lean source files were edited.
- No prior plan artifacts were modified.
- No commit was made.
