# PLAN 00: Current axiom frontier overview

**Status:** ACTIVE
**Goal:** prove every non-core project axiom without introducing new axioms, until only
the three Lean-core axioms and the single open research package
`MLC.residualOpenVirtualNearMoleculeAxiom` remain.

Human-facing companion: `notebooks/frontier_full_proof_roadmap.ipynb`
(rendered to `notebooks-html/frontier_full_proof_roadmap.html`).

## Verified frontier

`make check` reports `MLC.mlc_conjecture` is `sorry`-free and depends on three
Lean-core axioms (`Quot.sound`, `propext`, `Classical.choice`) plus **two** non-core
project axioms:

1. `MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling`
2. `MLC.residualOpenVirtualNearMoleculeAxiom`

**Dependency refresh:** `lake-manifest.json` now pins
`molecule-conjecture` to upstream revision
`385fc36c553947cf125d09848c2a3077fc751209`. The upstream refined export is now
a pair consisting of the operator package and canonical fast-fixed-point data;
the compatibility layer projects those components explicitly. The root-facing
Problem 4.3 uniform-bound target is kept as a direct residual interface because
the bound does not depend on a Molecule witness, so the upstream normalization
carrier does not enter the checked MLC proof.

**Update (2026-07, straddling refactor):** frontier axiom 1 was sharpened from
`green_sublevel_translate_inter_mandelbrot_connected` to a strictly weaker
`..._straddling` variant. The two nested strata of the intersection are now
discharged unconditionally — subset stratum via
`green_sublevel_translate_inter_mandelbrot_connected_of_subset` (core-clean) and
superset stratum via `..._of_superset` (off-path, from `mandelbrot_set_connected`).
The live frontier axiom asserts connectivity only where the Green-sublevel
translate is **not** contained in `M` (the equipotential boundary crosses `∂M`).

**Update (2026-07):** the earlier dynamical-plane seams
`MLC.Quadratic.green_function_strictMono_along_ray_basin_seam` and
`MLC.Quadratic.extended_ray_map_free_continuous` have been **removed from the
checked root path** (the sublevel connectivity they supported is now proved
directly by potential theory — Route A — see the corresponding section in
`README.md`), so the live
`make check` frontier is exactly the two axioms above.

### Literature correspondence (Dudko, arXiv 2512.24171)

- Axiom 1 (`green_sublevel_translate_inter_mandelbrot_connected`) ↔ the **Yoccoz
  parameter puzzle + Douady–Hubbard parameter↔dynamical correspondence**
  (§4.1–§4.2, Theorem 4.1 for the bounded-type/finitely-renormalizable cases).
  This is *established* mathematics — a Lean **formalization** gap, not open
  research. It has been localized (`green_sublevel_translate_connected`,
  `ParaPieceCarvedByMotion`) to the single Douady–Hubbard wringing/tubing carving
  motion; everything around it is proved and axiom-clean.
- Axiom 2 (`residualOpenVirtualNearMoleculeAxiom` =
  `Problem43PseudoSiegelAPrioriBoundsData ∧ Problem44VirtualMoleculeData`) ↔ the
  literature's **open** frontier: **Problem 4.3** (pseudo-Siegel a priori bounds
  in the remaining unbounded satellite ql cases) and **Interpolation Problem 4.4**
  (Virtual Molecule version of the Near-Degenerate Regime), reached through the
  §4.5 Virtual near-Molecule Renormalization setting. These are genuinely unsolved
  in the literature.

The former axiom `filled_julia_set_connected` is **discharged**
(`filled_julia_set_connected_proved`, `Mlc/FilledJuliaConnected.lean`) and no longer
appears in the checked frontier. The theorem
`proxy_bottcher_map_inj_on_basin_of_mem_mandelbrot` remains as a legacy
radial-proxy adapter; it still consumes the radial-monotonicity seam
`green_function_strictMono_along_ray_basin_seam`, and neither input is used by
the checked root path.

The former axiom pair `external_ray_map_exists` / `extended_ray_map_continuous` is
now represented by a legacy off-path boundary-continuity axiom
`extended_ray_map_free_continuous`. The *existence* of the external-ray
parameterization for `c ∈ M` is proved by
`GreenRayDischarge.external_ray_map_data_of_mandelbrot` (depends only on the
legacy radial ray seam); the checked connectivity proof uses the axiom-free
`external_ray_map_free` / `extended_ray_map_free` (in `BottcherAxioms.lean`), so
`external_ray_map_exists` no longer appears on the `mlc_conjecture` frontier. Only the
continuity to the unit circle remains axiomatic, and its statement is
`external_ray_map_exists`-free and restricted to `c ∈ M`.

A full formal proof means discharging axiom A (parameter-puzzle connectivity) as a
theorem (no new axioms) — a formalization of established Yoccoz/Douady–Hubbard
mathematics — leaving axiom B as the labelled open residual, and ultimately
discharging axiom B once the underlying open mathematics (Dudko Problems 4.3/4.4)
is available.

**Update (2026-08-30, Efimov route):** the Pacman/noncommutative-motive note is
now paired with the source-specific conditional plan
`plan/PLAN_05_MOTIVIC_ALTERNATIVE_AUDIT.md`, grounded in Efimov,
arXiv:2510.17010v1. Efimov supplies the relative localizing-motive,
rigidity, trace-class/nuclear refinement, and equivariant/local-system
interfaces, but not the finite phase-parameter realization, a conservative
separation-to-idempotent theorem, or motive indecomposability. The exact
frozen translated-Green comparison is also still missing, so the checked
frontier is unchanged.

The first Plan 05 gate is now checked by
`Mlc/MotivicIntersectionNoGo.lean`: a generic connected/open straddling
intersection rule is false, while a nontrivial clopen split yields a
nontrivial idempotent in `C(X, ℤ)`. This sharpens the required conservative
realization without changing the two-axiom frontier.

## Reduction architecture

- Local connectivity of `M` ← para-puzzle connectivity
  (`para_puzzle_piece_inter_mandelbrot_connected_proved`).
- Para-puzzle connectivity ← dynamical-plane Green-sublevel package (**now proved
  from core axioms only**, Route A below) + parameter-plane connectivity
  (**axiom 1**, `green_sublevel_translate_inter_mandelbrot_connected`).
- Infinite-branch / renormalization classification bottoms out at **axiom 2**
  (`residualOpenVirtualNearMoleculeAxiom` = Problems 4.3 + 4.4).

## SCOPE (2026-07): eliminate the radial-proxy root cause (route (a)) — ✅ COMPLETED

The two former dynamical-plane axioms (`extended_ray_map_free_continuous` and
`green_function_strictMono_along_ray_basin_seam`) existed **only** to make the
*radial proxy* `(z/‖z‖)·exp(G_c)` serve as a Böttcher coordinate in the one place
they were consumed: proving `green_sublevel_connected` (that `{G_c < ε}` is
connected for `c ∈ M`). This has been **fixed at the root** via Route A (direct
potential theory); both axioms are now off the checked frontier.

### Route A — direct potential theory (DONE)

Proves `IsConnected {z | G_c(z) < ε}` for `c ∈ M` **without any Böttcher/ray map**:

*Topological core.* Every connected component `U` of the open bounded set
`{G_c < ε}` has `Ū ∩ K_c ≠ ∅`: otherwise `U ⊆ basin` (disjoint from `K_c`, and
`G_c < ε` points are in `K_c ∪ basin`), `G_c` is harmonic on `U`, `G_c = ε` on
`∂U` (continuity + component), so the **minimum principle** forces `G_c ≥ ε` on
`U` — contradiction. Since `K_c ⊆ {G_c < ε}` is connected it lies in one
component `C₀`; any other component's closure meets `K_c ⊆ C₀`, forcing overlap —
so `{G_c < ε}` is connected. This achieved the *purpose* of the two dynamical
axioms at once; the entire radial-proxy machinery (`proxy_bottcher_map` inj seam,
`external_ray_map_free`, `extended_ray_map_free`, its continuity axiom) is now
**unused on-path** and both axioms have dropped. Achieved frontier: **2 non-core**
(axiom 1 param-connectivity + axiom 2 residual).

*Ingredients status.*
- ✅ `G_c` continuous (`continuous_green_function`); `{G_c=0}=K_c`
  (`green_function_eq_zero_iff_mem_K`); `K_c` connected for `c∈M`
  (`filled_julia_set_connected`, proved); `{G_c<ε}` bounded
  (`bounded_sublevel_green_function`, ParaPuzzleBasis); functional eqn
  `G_c(f z)=2 G_c z`.
- ✅ **LINCHPIN 1 — `G_c` harmonic on the basin.** DONE
  (`green_function_harmonicOnNhd_basin`): `G_c = lim 2^{-n} log‖f^n(·)‖` locally
  uniformly on the basin, each `log‖f^n‖` harmonic where `f^n ≠ 0`, harmonicity
  passing to locally-uniform limits via the mean-value property.
- ✅ **LINCHPIN 2 — harmonic minimum principle on a domain.** DONE (standalone,
  in the harmonic minimum-principle layer): a harmonic `u` attaining an interior
  min on a connected open set is constant.

*Outcome:* Linchpins 1–2 were genuine analysis builds but standard and
self-contained; both are now proved, so the two *unsound* radial-proxy axioms are
converted away and no longer appear on the checked frontier.

### Route B — genuine Böttcher biholomorphism (NOT pursued)

Build `φ_c : basin ≅ {|w|>1}` from the existing product scaffolding
(`BottcherProductAnalytic.correctionProductBottcherRatio`, analytic on the far
exterior) + the fact that `f_c` has **no critical point in the basin** for `c∈M`,
via a covering/monodromy degree-1 argument. This would discharge injectivity but
**cannot** discharge boundary continuity: continuous boundary landing at `|w|=1`
is Carathéodory extension = local connectivity of `J(c)`, which is **open / false
for some `c∈M`**. Dominated by Route A, which was pursued and completed.

**Status: Route A completed. Both dynamical-plane axioms discharged.**

## Feasibility tiers (current 2-axiom frontier)

| Axiom | Content | Tier | Feasibility |
|---|---|---|---|
| A. `green_sublevel_translate_inter_mandelbrot_connected` (parameter-puzzle connectivity) | Yoccoz puzzle + Douady–Hubbard parameter↔dynamical correspondence, `c ∈ M` | C | **Established mathematics; Lean-formalization gap only.** Localized to a single Douady–Hubbard carving motion (`ParaPieceCarvedByMotion`); everything around it proved and axiom-clean |
| B. `residualOpenVirtualNearMoleculeAxiom` (= Problems 4.3 ∧ 4.4) | Dudko–Lyubich Virtual near-Molecule program | D | **Open research** — not feasible now (Problem 4.3 pseudo-Siegel bounds; Interpolation Problem 4.4) |

*Discharged (historical):* filled-Julia connectivity, proxy-Böttcher injectivity,
external-ray existence, external-ray boundary continuity, radial Green
monotonicity — all removed from the checked frontier (see `README.md`).

- **Tier A** — known mathematics, machinery already partially in the repository.
- **Tier B** — feasible after an interface refactor or a parameter restriction.
- **Tier C** — known mathematics needing large missing foundations (or only available
  on a sub-stratum of parameters).
- **Tier D** — genuine open research frontier; formalization is blocked on the
  underlying mathematics not being complete.

## Per-axiom status and route

> **⚠️ HISTORICAL SECTION (superseded).** Everything from here to the
> "Tier C — axiom A" heading below is the detailed analysis of the old
> radial-proxy axioms (external-ray existence, external-ray boundary continuity,
> radial Green monotonicity). **These inputs have been removed from the checked
> root path, not proved by the direct Route-A bypass** (see the corresponding
> record near the end and `README.md`). The notes are retained only as a record of why the
> radial-proxy route was abandoned in favour of direct potential theory (Route A).
> The live frontier is exactly axioms **A** and **B**.

### ⛔ CRITICAL (2026-07): axiom 2 is ALSO UNSOUND for `c ∈ M`

**`extended_ray_map_free_continuous` is mathematically FALSE** — same radial-proxy
root defect. By definition `extended_ray_map_free c w = fixed_point c` for every
`w` on the unit circle (`‖w‖ = 1`), a **single constant point**. `ContinuousOn` on
`{w | 1 ≤ ‖w‖}` therefore forces *every* origin-ray to land at that one point.
But the actual ray landings vary widely with direction:

| c | landing-point spread over 8 directions |
|---|---|
| basilica `-1` | 3.24 |
| rabbit `-0.1226+0.7449i` | 2.18 |

(landings e.g. `1.62+0i`, `0.36+0.36i`, `0+0.79i`, `-0.36+0.36i` for basilica).
So the constant-boundary-value continuity claim is false. This mirrors the old
`extended_ray_map_continuous` and is inseparable from the axiom-3 defect: both are
artifacts of using the *radial* proxy `(z/‖z‖)·exp(G_c(z))` instead of the genuine
Böttcher coordinate `φ_c`. **Fixing the radial proxy (route (a) below) discharges
the root cause of both axioms 2 and 3 simultaneously.**

Axiom 4 (`green_sublevel_translate_inter_mandelbrot_connected`), by contrast, shows
**no soundness red flag**: numerically the translated sublevel `∩ M` is one large
connected component (>99% of sampled points; residual 1–2-pixel specks are
fractal-boundary grid noise). It remains hard (λ-lemma foundation) but plausibly
true, not false.

### ⛔ CRITICAL (2026-07): axiom 3 is UNSOUND for `c ∈ M`

**`green_function_strictMono_along_ray_basin_seam` is mathematically FALSE.**
Numerical counterexample (stable across escape radius `R = 1e6…1e18`, iteration
cap `N = 80…400` — i.e. *not* a quantization artifact), Douady rabbit
`c = -0.122561 + 0.744862i ∈ M`, real direction `u = 1`:

| ρ | escapes at | `G_c(ρu)` |
|---|---|---|
| 0.390 | n=17 | 2.458e-04 |
| 0.396 | n=17 | **2.631e-04** |
| 0.405 | n=18 | **1.627e-04** |
| 0.437 | n=15 | 8.552e-04 |

`G` strictly *decreases* from ρ=0.396 to ρ=0.405 while both points are in the
basin (both escape). The origin-ray even leaves the basin and re-enters `K(c)`
(the rabbit's `K` is not star-shaped about `0`). Basilica `c=-1`, `c=-0.75`,
`c=-1.25` all violate radial monotonicity too; only `c=0` satisfies it.

**Consequences.**
1. The equipotentials `{G_c = const}` are **not star-shaped about `0`** for
   general `c ∈ M`, so radial Green monotonicity along origin-rays is false.
2. Therefore the **radial** proxy `φ(z) = (z/‖z‖)·exp(G_c(z))` is **NOT injective**
   on the basin: two distinct radii on the same ray share direction *and*
   modulus `exp(G)`, hence the same proxy image. So the derived theorem
   `proxy_bottcher_map_inj_on_basin_of_mem_mandelbrot` is provable **only because
   it consumes the false seam axiom**.
3. Axiom 3 **cannot be discharged**; the whole *radial-proxy* substitution for the
   Böttcher coordinate is unsound for the injectivity/connectivity argument.

**Correct route (redirect, not a discharge).** Replace the radial proxy by the
*genuine* Böttcher coordinate `φ_c : basin → {|w|>1}`, the biholomorphism with
`|φ_c| = exp(G_c)` and `φ_c' ≠ 0`. Its injectivity is real (it is a
biholomorphism) and needs no radial monotonicity. This is a substantial refactor:
formalize `φ_c` (holomorphic, non-vanishing derivative, conformal to the exterior
disk) and rebuild `GreenSublevelJoinedToKc`/`ParaPuzzleConnectivity` on `φ_c`
instead of the radial proxy. Until then, axiom 3 must be flagged **unsound**, not
"high-feasibility". The earlier "large-ratio island" / "small-gap obstruction"
analysis below is now moot: the small-gap regime is not merely hard, the target
statement is *false*.

### Tier A — axiom 3 (`green_function_strictMono_along_ray_basin_seam`) — proxy injectivity DISCHARGED

The proxy Böttcher map is the **radial** proxy `(z/‖z‖)·exp(G_c(z))`, so it is *not*
holomorphic (its phase is `arg z`, not the true Böttcher phase). Its basin
injectivity is therefore elementary and does **not** need analyticity/local
homeomorphism. This is now the checked theorem
`proxy_bottcher_map_inj_on_basin_of_mem_mandelbrot`, built from the reusable
`proxy_bottcher_map_injOn_nonzero_basin_of_green_ray_strictMono`: equal images force
equal modulus `exp(G_c)` (hence equal Green value) and equal direction `z/‖z‖`, and
strict Green monotonicity along the common origin-ray forces equal radii; for `c ∈ M`
the critical point stays in `K(c)` so `0 ∉ basin`.

The residual is the radial-monotonicity seam
`green_function_strictMono_along_ray_basin_seam`. It is now **reduced** (not yet
discharged) to a single orbit-geometry statement by the checked lemma
`green_function_lt_of_escaping_of_orbit_ratio_tendsto_atTop` (in
`GreenFunctionRayInversion.lean`): for any `c` and any two escaping points along a
straight origin-ray, if the orbit-norm ratio `‖orbitⁿ(ρ₂u)‖/‖orbitⁿ(ρ₁u)‖ → ∞` then
`G_c(ρ₁u) < G_c(ρ₂u)`. This is the direction-free core of the constructive `c = 2`
real-ray proof (`green_function_strictMono_along_real_ray_two`): the functional
equation `G(orbitⁿ) = 2ⁿ·G` and the uniform far-field bound `|G − log‖·‖| ≤ M` supply
everything except the ratio hypothesis, which is the sole geometry-specific ingredient.
The seam-shaped corollary is `green_function_strictMono_along_ray_of_orbit_ratio`.

**Remaining residual (the sharp open sub-problem):** prove the orbit-ratio blow-up for
general `c ∈ M` and general direction `u`. At `c = 2` this is available for real
directions via explicit real-dynamics growth (`f2_ratio_tendsto_atTop`, an
`(16/9)ⁿ`-type bound independent of `G`); for non-real directions and general `c` no
`G`-independent orbit-ratio bound is yet in the repo. Note the naive route "`ratio → ∞`
from `G(z₂) > G(z₁)`" is **circular** (`‖orbitⁿ z‖ ≈ exp(2ⁿ G(z))`; the existing
`OrbitNormRatio.norm_orbit_two_ratio_tendsto_atTop_along_ray` derives the ratio *from*
Green monotonicity, so it cannot be used to prove it).

**Quantified obstruction (why a direction-agnostic proof fails).** The only
direction-independent handle on the complex orbit is the crude norm recursion
`‖z²+2‖² ∈ [‖z‖⁴−4‖z‖²+4, ‖z‖⁴+4‖z‖²+4]`. Writing `Sₙ = (‖orbitⁿ(t₂u)‖/‖orbitⁿ(t₁u)‖)²`,
the adversarial (worst-case direction) recursion `Sₙ₊₁ ≥ Sₙ(Sₙ−¼)/(1+¼+…)` has a
**repelling fixed point at `S* ≈ 1.516` (ratio ≈ 1.231)**: for `S₀ < S*` it collapses
(`b ≤ a` within one step), for `S₀ > S*` it blows up. Numerically the *true* ratio
blows up for every gap, but the crude bound provably cannot certify the small-gap
regime — the regime injectivity actually needs (two distinct radii with `t₂/t₁ → 1`).
A constructive discharge must therefore track the genuine direction dynamics,
equivalently that the `c = 2` equipotentials are star-shaped about `0`. Consequence:
the **large-ratio** case (`t₂² ≥ 2 t₁²`, i.e. `t₂ ≳ 1.41·t₁`) is now constructively
**proven** — Green-free — by
`OrbitNormRatio.norm_orbit_two_ratio_tendsto_atTop_along_ray_of_large_ratio` (crude
two-sided step bound `orbit_two_norm_sq_step` + the multiplicative-growth inequality
`large_ratio_poly`, giving a `2·(21/16)ⁿ` squared-ratio lower bound), wired to Green
monotonicity by `OrbitNormRatio.green_function_strictMono_along_ray_two_of_large_ratio`
via `green_function_lt_of_escaping_of_orbit_ratio_tendsto_atTop`. This island does
**not** close the axiom: the small-gap regime (`t₂/t₁ → 1`), which injectivity actually
needs, remains blocked by the repelling-fixed-point obstruction above. The earlier
"base-region log-series analyticity" route was a **dead end** for this axiom: proxy
holomorphy is neither available (far-exterior slit obstruction at `c = 2`) nor needed.

### Tier A/B — axiom 1 (`external_ray_map_exists`)

**CRITICAL OBSTRUCTION (this session): the `c = 2` target is FALSE, so the
long-standing "discharge axiom 1 at `c = 2`" plan is a dead end.**

`external_ray_map_exists (c : ℂ) : ExternalRayMapData c` demands, for *every* `c`, a
full right inverse of `proxy_bottcher_map c` on all of `{‖w‖ > 1}` (the first conjunct of
`ExternalRayMapDataFor`). But `c = 2` lies *outside* the Mandelbrot set: its Julia set is
a Cantor set, and the radial rays never approach it, so `green_function 2` has a strictly
positive minimum along every ray. Numerically `min_ρ G_2(ρ·u) ≈ 0.45` along the real
direction and `≥ 0.022` across all directions; along the real axis every point escapes
(`x² + 2 > x`), so `G_2 > 0` there identically. Consequently
`proxy_bottcher_map 2 z = (z/‖z‖)·exp(G_2 z)` cannot hit any `w` with
`1 < ‖w‖ < exp(min_ρ G_2(ρ·u))` in direction `u = w/‖w‖`. Hence
`proxy_bottcher_map 2` is **not surjective onto `{‖w‖ > 1}`** and `ExternalRayMapData 2`
is **false**. The whole `..._via_green_function` chain is gated on the anchor hypothesis
`hlog_gt_anchor : ∀ w, 1<‖w‖ → G_2(4·(w/‖w‖)) < log‖w‖`, which is likewise false as
`‖w‖ → 1⁺` (`log‖w‖ → 0⁺` while `G_2(4u)` has a positive compact-circle minimum).

Since the axiom is stated `∀ c`, removing the `axiom` keyword would require proving the
false `c = 2` instance — impossible. **The axiom is therefore unsound as stated.**

*Status of the two ingredients:*
- Injectivity on `{‖z‖ > 4}` is already a theorem
  (`injOn_outside_open_two_of_green_function_ray_strictMono`, from the strict-mono seam);
  no gap here.
- Surjectivity is the true (and, at `c = 2`, unattainable) blocker.

**MATH DISCHARGED for `c ∈ M`, axiom-clean (this session).** The restricted statement is
now a *proved theorem* — `MLC.GreenFunctionRayInversion.external_ray_map_data_of_mandelbrot`
`(c : ℂ) (hc : c ∈ MandelbrotSet) : ExternalRayMapData c` in
`GreenFunctionRayInversion.lean`. It compiles, the full `make build`/`make check`/
`verify_output.sh` stay green, and `#print axioms` confirms it depends on **only** Lean-core
axioms plus **axiom 3** (`green_function_strictMono_along_ray_basin_seam`) — crucially
**not** on `external_ray_map_exists` (no circularity) and **not** on `bottcher_seq_converges`.
The proof rests on the key enabler that for `c ∈ M` the critical value `0 ∈ K c`, so
`green_function c 0 = 0`; every origin ray then sweeps `G` over `(0, ∞)` and IVT anchored
at `ρ = 0` gives surjectivity of the radial proxy onto `{‖w‖ > 1}` (direction `w/‖w‖`,
modulus `exp(G)=‖w‖`) with no monotonicity needed. Injectivity on `{‖z‖ > ‖c‖+2}` comes
from axiom 3. The `ExternalRayMapData` package (right-inverse on `{‖w‖>1}` + left-inverse
on the outside region) is assembled **directly** — bypassing the earlier
`BasinExternalRayMapDataFor` constructor, whose `φ(f z)=(φz)²` conjugation hypothesis is
**false** for the radial proxy and is only provable via the (also false)
`bottcher_seq_converges` axiom. Supporting axiom-clean lemmas:
`exists_ray_preimage_green_of_mandelbrot`, `surjOn_proxy_bottcher_map_of_mandelbrot`,
`injOn_proxy_bottcher_map_outside_open` (general `c`).

**Important side finding: `bottcher_seq_converges` is UNSOUND as stated.** It asserts the
principal-branch `2^n`-th-root sequence `((·²+c)^[n] z)^(1/2^n)` converges locally
uniformly to the *radial* `proxy_bottcher_map c`. Numerically the principal-root limit is
`exp(G_c z)` (a positive **real**), not `(z/‖z‖)·exp(G_c z)`; they agree only when `z` is
positive real. So the radial proxy does **not** satisfy the Böttcher functional equation
(only its modulus part), and `bottcher_seq_converges` / `bottcher_conj_on_basin` are false
off the real axis. They are currently **off** the `mlc_conjecture` critical path; the
axiom-clean discharge above deliberately avoids them.

**Remaining work to actually REMOVE axiom 1 from the checked frontier: a layering
refactor only (now a genuine 5→4 reduction, no axiom swap).** `external_ray_map` and
`bottcher_domain` are *defined inside* `BottcherAxioms.lean` using the axiom, and the
on-path connectivity proof (`GreenSublevelJoinedToKc.green_sublevel_joined_to_Kc`)
constructs basin paths *from* `external_ray_map`. So `#print axioms mlc_conjecture`
inherits the axiom through those *definitions*. Dropping it requires **redefining**
`external_ray_map` axiom-free as
`if hc : c ∈ MandelbrotSet then external_ray_map_of_data (…_of_mandelbrot c hc) w else 0`,
which needs `external_ray_map_data_of_mandelbrot` (and its axiom-clean ingredients)
available **upstream** of `BottcherAxioms`. Since the discharge now depends only on axiom 3
(already in the frontier), completing this extraction is a genuine reduction. The
analyticity work in `BottcherProductAnalytic.lean` remains auxiliary.

**Concrete, fully-scoped refactor plan (feasibility CONFIRMED this session).** Two facts
weld axiom 1 to `mlc_conjecture`: (i) the connectivity proof builds paths from the
axiom-based `external_ray_map`; (ii) **axiom 2 (`extended_ray_map_continuous`) is itself
stated via `extended_ray_map → external_ray_map`**, so `#print axioms` on axiom 2 already
lists `external_ray_map_exists`. Removing axiom 1 therefore requires *both* an axiom-free
`external_ray_map` *and* an axiom-1-free restatement of axiom 2. Verified feasible:
- *Upstream extraction file* `Mlc/.../Bottcher/GreenRayDischarge.lean` importing only
  `{BottcherCore, Axioms, Yoccoz.Green/GreenLemmas/Escape, Mathlib.IntermediateValue}`.
  All ingredient helpers are elementary and axiom-1-free — `outside_disk_subset_…`,
  `green_function_pos_of_basin`, `large_norm_mem_outside_disk`,
  `green_function_pos_on_outside_open`, `green_function_strictMono_along_ray_basin`
  (wraps axiom 3), `exists_ray_preimage_green_of_mandelbrot`, `surjOn_…`, `injOn_…`,
  `external_ray_map_data_of_mandelbrot` — but several currently live *downstream*
  (`BottcherOnMTheory`/`BottcherOutsidePlan`) and must be **reproved** upstream (each
  bottoms out in Yoccoz escape/green facts, e.g. `iterate_quadratic_map_tendsto_infty`,
  `green_function_pos_iff_not_mem_K`).
- *`BottcherAxioms` surgery*: import the new file; replace `axiom external_ray_map_exists`
  with the dite-guarded axiom-free `external_ray_map`; likewise axiom-free
  `extended_ray_map`; **restate axiom 2** about the new `extended_ray_map`; add `hc : c∈M`
  to `external_ray_map_right_inverse`, `..._left_inverse_large`, `bottcher_left_inv`,
  `..._left_inverse_outside_open`, `external_ray_map_data`.
- *Threading*: reroute the on-path files — `GreenSublevelJoinedToKc` (31 refs, the
  path-construction proof), `GreenSublevelConnected` (3), `ParaPuzzleConnectivity` (10),
  `MainConjecture` (7) — passing `hc` (in scope at each on-path use). Off-path generic-`c`
  consumers (`BottcherRayMap`, `DegreeOneInj`, `InverseBranchSlitUse`,
  `BottcherOnM*`/`BottcherOutsidePlan`, ~250 refs) break under the redefinition and must
  either receive `hc` or be moved onto a preserved axiom-based alias.
- *Cost/risk*: multi-hour, ~4 on-path files + extraction file rewritten, hundreds of
  off-path refs to audit; convergent but with extended build-breakage risk. This is the
  sole remaining barrier to a checked 5→4 frontier; the mathematics is done.

*Superseded note (kept for context):* At the root there are checked constructors
(`external_ray_map_data_two_of_isClosedRange_restrict_of_analyticAt_of_injOn_outside_open`
and siblings) reducing existence to analyticity + injectivity + closed-range/quotient
rigidity, and a constructive scaffold in `BottcherOutsidePlan.lean`
(`finiteProductBottcherRatio` / `correctionProductBottcherRatio`) with analyticity landed
in `BottcherProductAnalytic.lean`. These remain valid building blocks but do **not**
resolve the `c = 2` surjectivity falsity above; they must be redirected to `c ∈ M`.

### Tier C — axiom A (`green_sublevel_translate_inter_mandelbrot_connected`) — LIVE

Parameter-plane Yoccoz puzzle connectivity; standard proof via holomorphic motions
and the Słodkowski / λ-lemma + the Douady–Hubbard parameter↔dynamical
correspondence. **Established mathematics**, but Mathlib lacks the λ-lemma
foundation, so this is a large formalization build (not open research).

*Current localization (this repo):* the un-intersected translate
`{c' | G_c(c'-c) < 2^{-n}}` is **proved connected** from core axioms only
(`green_sublevel_translate_connected`); the residual is exactly the `∩ M` carving,
reduced to a single space-holomorphic motion
(`Mlc/ParaPuzzleCarvingReduction.lean`, `ParaPieceCarvedByMotion`). The Słodkowski
statement layer + a c-holomorphic parametrized Böttcher inverse (via a ℂ² inverse
function theorem) are built and axiom-clean (`Bottcher/Slodkowski.lean`,
`Bottcher/BottcherParamInverse.lean`). The remaining ingredient — the actual
Douady–Hubbard wringing map — is Yoccoz-scale.

### Tier D — axiom B (`residualOpenVirtualNearMoleculeAxiom`) — LIVE, OPEN

`Problem43PseudoSiegelAPrioriBoundsData ∧ Problem44VirtualMoleculeData`:
pseudo-Siegel a priori bounds in the remaining unbounded satellite ql cases
(**Problem 4.3**) and the virtual Molecule near-degenerate interpolation regime
(**Interpolation Problem 4.4**). This is the **open** Dudko–Lyubich near-Molecule
program (arXiv 2512.24171, §4.5); the mathematics itself is not complete in the
literature. Keep it as the single labelled residual; do not expand it with new
theorem-hook axioms.

## Discharged axioms (historical record)

The following were on earlier frontiers and are now **off** the checked frontier:

- `filled_julia_set_connected` → theorem (`Mlc/FilledJuliaConnected.lean`).
- proxy-Böttcher basin injectivity → theorem
  (`proxy_bottcher_map_inj_on_basin_of_mem_mandelbrot`).
- `external_ray_map_exists` / `extended_ray_map_continuous` → replaced then
  eliminated via the axiom-free `c ∈ M` ray map + Route A.
- `extended_ray_map_free_continuous` and
  `green_function_strictMono_along_ray_basin_seam` → dropped: the sublevel
  connectivity they supported is proved directly by potential theory (Route A,
  `green_sublevel_connected_direct`).

**Soundness note (important history):** several of the discharged proxy axioms were
*unsound as originally stated* (e.g. radial Green monotonicity is false for some
`c ∈ M` — the rabbit's real ray falsifies it; and the `∀ c` ray-existence form is
false at `c = 2`). They were not "discharged" by proving a false statement — they
were **removed** by replacing the radial-proxy route with genuine potential theory
restricted to `c ∈ M`. Future work must preserve this: never reintroduce a `∀ c`
proxy-coordinate axiom.

## Validation policy

After each frontier reduction run `make build`, `make check`, and
`./scripts/verify_output.sh`; update `README.md` and `check_axioms.lean` if the frontier
changed; rerender notebooks with `make notebook-render`.

## Honesty note

A fully axiom-free formal proof of MLC is **not currently attainable**: axiom B
encodes mathematics (Dudko Problems 4.3/4.4) that is itself open. Axiom A is
established mathematics but a substantial Mathlib/λ-lemma formalization gap; it has
been localized to a single Douady–Hubbard carving motion but not discharged.
Record blockers explicitly rather than implying full proof is imminent.
