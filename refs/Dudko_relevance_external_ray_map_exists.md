# Dudko Works Download + Relevance Note

Date: 2026-02-20

## Downloaded into `refs/`

ArXiv / open PDFs downloaded:
- `Dudko_2512.24171.pdf` (ICM note, includes 2025/2026 status)
- `Dudko_2509.25658.pdf`
- `Dudko_2509.23031.pdf`
- `Dudko_2407.15548.pdf`
- `Dudko_2309.02107.pdf`
- `Dudko_2210.09280.pdf`
- `Dudko_2209.02800.pdf`
- `Dudko_1808.10425.pdf`
- `Dudko_1802.03045.pdf`
- `Dudko_1703.01206.pdf`
- `Dudko_1610.02434.pdf`
- `Dudko_1603.04059.pdf`
- `Dudko_1512.08539.pdf`
- `Dudko_1512.05948.pdf`
- `Dudko_1412.8760.pdf`
- `Dudko_1112.4780.pdf`
- `Dudko_1004.0633.pdf` (Decoration theorem preprint)
- `Dudko_S0002-9939-2011-11047-5.pdf` (Homeomorphisms between limbs)

Notes:
- Direct JSTOR/OUP endpoints from the publication list returned anti-bot/403 in CLI.
- For "Homeomorphisms between limbs", AMS PDF was obtained directly.
- For "Decoration theorem", open preprint `arXiv:1004.0633` was obtained.

## Relevance to current elimination (`external_ray_map_exists`)

Current formal blocker in codebase:
- Prove non-circularly at `c = 2`:
  - outside-open injectivity of `bottcher_map`, and
  - restricted-map closed-range/properness payloads,
  so that `BottcherSurjOnExteriorFromOutsideOpen (2 : ℂ)` can replace the axiom path.

### Highest relevance (strategy-level, not direct theorem drop-in)
- `2512.24171` (ICM status note): broad roadmap for MLC via renormalization.
- `2309.02107` (MLC at Feigenbaum points): a priori bounds -> local connectivity at IR class.
- `1808.10425` (satellite bounded type): local connectivity at additional IR classes.

Why useful:
- They support a Track-1/Track-2 pivot (renormalization/classification route), which can reduce dependence on an external-ray axiom in global strategy.

### Medium relevance
- `1004.0633` (Decoration theorem): geometric control in parameter space; may support local-connectivity style arguments and puzzle geometry.
- `Dudko_S0002-9939-2011-11047-5.pdf` (limb homeomorphisms): combinatorial/parameter-space structure.

### Low relevance to the *specific* current Step-3/4 target
- Neutral renormalization papers (`2210.09280`, `2509.23031`), disjoint-type hyperbolic bounds (`2509.25658`),
- branched-covering algorithmic series (`1512.*`, `1603.*`, `1610.*`, `1802.*`),
- correspondences decomposition (`2407.15548`),
- pacman/core-entropy/matings (`1703.01206`, `1412.8760`, `1112.4780`).

These do not appear to directly supply the exact theorem form currently needed in Lean:
- `Set.InjOn (Quadratic.bottcher_map (2 : ℂ)) {z | ‖z‖ > ‖(2 : ℂ)‖ + 2}`
- `IsClosed (Set.range (bottcher_map_outside_open_to_exterior (2 : ℂ)))` (or `IsProperMap`)
without circular external-ray assumptions.

## Practical conclusion
- Useful Dudko material exists for a renormalization/classification-based MLC path.
- No immediate direct replacement theorem was identified for the current outside-open injectivity/closed-range subgoal.
- If we stay on the current elimination route, we still need a new non-circular analytic/topological proof of Step 3/4 in the present formal model.
