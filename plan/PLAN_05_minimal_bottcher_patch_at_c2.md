# PLAN 05: Minimal Böttcher Patch at c=2

**Status:** `░░░░░░░░░░` **0%**
**State:** `PROPOSED`
**Difficulty:** Medium
**Risk:** Low-Medium — scoped to c=2, minimal changes to existing code.

## Core Idea

The most surgical fix: keep the crude `bottcher_map` definition but
introduce a **correct specialized Böttcher map at c=2** alongside it.
Then prove `ExternalRayMapData (2)` in terms of the crude map by
constructing a right inverse that compensates for the angle error.

## Key Mathematical Insight

The crude `bottcher_map c z = (z/|z|) · exp(G(c,z))` and the true
Böttcher coordinate `φ_c(z)` share the same modulus: `|φ_c(z)| = exp(G(c,z))`.
They differ only in the angular part.

Let `θ(c, z)` be the angular correction: `φ_c(z) = e^{iθ(c,z)} · (z/|z|) · exp(G(c,z))`.
Then: `bottcher_map c z = e^{-iθ(c,z)} · φ_c(z)`.

For `ExternalRayMapData c` (right inverse of `bottcher_map c`), we need
`f : ℂ → ℂ` with `bottcher_map c (f w) = w` for |w| > 1.

Let `ψ_c = φ_c⁻¹` (inverse of true Böttcher coordinate). Then:
```
bottcher_map c (ψ_c(e^{iθ(c, ψ_c(w))} · w)) = w
```

Wait — this gets circular. Let me think differently.

## Simpler Approach: Redefine Only `ExternalRayMapData`

Instead of fixing `bottcher_map`, weaken the requirement. The proof chain
uses `ExternalRayMapData` only to get `BottcherSurjOnExterior`:

```lean
BottcherSurjOnExterior c = ∀ w, 1 < ‖w‖ → ∃ z, bottcher_map c z = w
```

And from `BottcherSurjOnExterior (2)` the chain derives `False`.

**So the real problem is**: the proof from `BottcherSurjOnExterior` to MLC
goes through `False.elim`. No matter how we get `BottcherSurjOnExterior (2)`,
the proof chain still derives False and then MLC.

If we could get `BottcherSurjOnExterior (2)` constructively (without the
axiom), we'd have an axiom-free proof of MLC. But
`BottcherSurjOnExterior (2)` is FALSE for the crude map.

## Radical Idea: Don't Prove BottcherSurjOnExterior(2)

The proof chain ultimately only needs `MainPathData`. Currently this is
obtained via `BottcherSurjOnExterior → False → MainPathData`.

What if we get `False` from a DIFFERENT source that doesn't require
the axiom?

### Looking for Existing Inconsistencies

If the formalization already has an inconsistency (without the axiom), we
could exploit it. But this is:
(a) Unlikely — the code has been validated with `make check`
(b) Bad mathematics (even if it works formally)
(c) Would mean the formalization is buggy

### Alternative: Prove MainPathData Without False

Route:
```lean
theorem mlc_conjecture : LocallyConnectedSpace mandelbrotSet := by
  exact mlc_conjecture_of_mainPathData ⟨h_motion, h_track12⟩
```

This requires constructively proving `PuzzleBoundaryMotionHyp` and
`IRNoTowerPrimitiveAndMoleculeBridgeTargetData` — which is Plan 02.

## Revised Plan: Angle-Corrected Right Inverse at c=2

Define a function that maps {|w| > 1} to ℂ such that applying the crude
`bottcher_map 2` gives back `w`. The function must:
1. For each w with |w| > 1, find z such that:
   - `z/|z| = w/|w|` (same direction as w)
   - `G(2, z) = log|w|` (correct Green function value)

Condition 1 means z lies on the ray from 0 in direction `w/|w|`.
Condition 2 means z is at the right "Green distance" from K(2).

For this to work, we need: for every unit direction u and every target
value t > 0, there exists z on the ray in direction u (i.e., z = ρ·u,
ρ > 0) with G(2, ρ·u) = t.

This is exactly the Green function radial surjectivity along each direction.
For the Green function at c=2, along each direction u, the function
ρ ↦ G(2, ρ·u) is:
- Continuous on (0, ∞)
- → ∞ as ρ → ∞ (points far from K(2) have large G)
- → 0 if the ray in direction u passes through K(2) at some ρ₀
  (then G(2, ρ₀·u) = 0 for ρ₀ ∈ K(2))

For direction u where the ray hits K(2), the IVT gives surjectivity onto
(0, ∞).

For direction u where the ray DOESN'T hit K(2) (e.g., u = 1, the real
positive direction — since K(2) has no real points), G(2, ρ·u) > 0 for
all ρ > 0. The minimum value of G along this ray may be bounded away from 0.
In that case, there's a minimum Green value g_min > 0, and the right
inverse only exists for |w| > exp(g_min).

**This means `BottcherSurjOnExterior (2)` is FALSE even with the IVT
approach**, because along certain directions the Green function doesn't
reach all positive values. Specifically, along the real direction:

- `G(2, ρ) → G(2, 0) > 0` as ρ → 0⁺ (since 0 escapes for c=2)
- `G(2, ρ) → ∞` as ρ → ∞
- The minimum of `G(2, ρ)` for real ρ > 0 is some g_min > 0

So the crude bottcher_map misses the annulus `1 < |w| < exp(g_min)` along
the real direction. This is consistent with the contradiction proof.

## Final Assessment

This plan confirms that **no patch to the crude `bottcher_map` can achieve
surjectivity at c=2**. The angular error makes the map non-surjective near
the unit circle in certain directions.

The only viable paths are:
1. **Fix the definition** (Plans 01, 03)
2. **Bypass the Böttcher map** (Plan 02)
3. **Find a new proof architecture** (Plan 06)
