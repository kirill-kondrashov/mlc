# Progress toward eliminating `green_sublevel_translate_inter_mandelbrot_connected`

## Exact objective

Remove the live axiom

```lean
MLC.green_sublevel_translate_inter_mandelbrot_connected_straddling
```

and ensure the downstream local-connectivity route no longer depends on it or on
an equivalent replacement axiom.

The unrestricted theorem
`green_sublevel_translate_inter_mandelbrot_connected` is already a theorem, but
its straddling branch calls that axiom.

## Progress table

| Status | Layer | Progress | Evidence |
|---|---|---:|---|
| ✅ | Dynamical filled Julia connectivity | 🟩🟩🟩🟩🟩 100% | `filled_julia_set_connected` is proved without the old axiom |
| ✅ | Dynamical Green-sublevel connectivity | 🟩🟩🟩🟩🟩 100% | `GreenSublevelConnectedDirect.lean` |
| ✅ | Translated Green sublevel connectivity | 🟩🟩🟩🟩🟩 100% | `green_sublevel_translate_connected` |
| ✅ | Nested subset stratum | 🟩🟩🟩🟩🟩 100% | `...connected_of_subset` |
| ⚠️ | Superset stratum | 🟩🟩🟩🟩⬜ 80% | proved, but uses axiomatic `mandelbrot_set_connected` and is off the main split |
| ❌ | Straddling frozen-base intersection | ⬜⬜⬜⬜⬜ 0% | remains exactly the live frontier axiom |
| ✅ | Exact-image carving route audit | 🟩🟩🟩🟩🟩 100% | formally refuted on the straddling case |
| ✅ | Motion-image packaging audit | 🟩🟩🟩🟩🟩 100% | proved equivalent to target connectivity, hence not a reduction |
| ✅ | Numerical falsifiability screening | 🟩🟩🟩🟩🟩 100% | no robust counterexample, but no proof |
| ✅ | Literature exact-match audit | 🟩🟩🟩🟩🟩 100% | classical parapuzzles use moving parameter geometry, not frozen `G_c(c'-c)` |
| 🟡 | Genuine parameter-piece replacement | 🟩⬜⬜⬜⬜ 20% | Route-C construction selected; actual equipotential/parapuzzle object and API still to be specified |
| ✅ | Local Böttcher inverse motion base | 🟩🟩🟩🟩🟩 100% | `BottcherParamMotion.lean`: nontrivial space-holomorphic motion of an explicit connected disk with a uniform inverse identity |
| ⬜ | Downstream interface migration | ⬜⬜⬜⬜⬜ 0% | `ParaPuzzlePieceAt` still reduces to frozen Green translate |
| ⬜ | Delete straddling axiom | ⬜⬜⬜⬜⬜ 0% | final milestone |

## Route diagram

```text
CURRENT, BLOCKED ROUTE

fixed-map Green sublevel
        │
        ├── ✅ connected before intersecting M
        │
        ▼
frozen translate ∩ MandelbrotSet
        │
        └── ❌ straddling connectivity has no verified classical theorem


RECOMMENDED ROUTE

parameter rays/equipotentials + moving critical orbit
        │
        ▼
genuine finite-level parapuzzle component
        │
        ├── sourced component/topology theorem
        ▼
connected relative parameter piece
        │
        ▼
LcAtOfShrink-compatible family
        │
        ▼
remove frozen-target dependency and delete straddling axiom
```

## Honest interpretation of “discharge”

There are two possible meanings:

1. **Prove the exact frozen-base theorem.** No verified source currently supports
   it, and the existing audits found no bridge from classical parapuzzles. This
   would require new mathematics specific to the repository's set.
2. **Discharge it from the MLC dependency graph.** Replace the artificial frozen
   parameter piece by a genuine moving-parameter parapuzzle object, prove the
   consumer from that object, then delete the unused theorem and axiom.

The moving-parameter Route-C construction is currently the only sourced,
credible path. Its local Böttcher inverse/motion base is checked, but the
actual finite-level parameter piece and its correspondence theorem are not.

## New checked Route-C brick

`Mlc/Quadratic/Complex/Bottcher/BottcherParamMotion.lean` extracts a
positive-radius local motion from `exists_param_holo_bottcher_inverse`. Its
source is a closed disk and its slices are explicit translations, so
space-holomorphy, injectivity, source connectedness, and nontriviality are
proved without a new axiom. The local inverse recovers the translated point
along a simultaneous parameter/dynamical path.

This is intentionally not presented as the required parapuzzle boundary:
there is still no theorem identifying the disk with an equipotential, a moving
parameter piece, or the frozen target intersected with `M`. The straddling
frontier therefore remains unchanged.

## Prompt forecast

| Milestone | Estimated worker prompts |
|---|---:|
| Pin exact genuine finite-level parameter piece and source theorem | 1–2 |
| Compile minimal Lean parameter-graph/component definition | 2–4 |
| Prove elementary component connectedness and relative-neighborhood API | 1–3 |
| Connect sourced phase–parameter theorem | 4–10+ |
| Migrate `LcAtOfShrink` consumer and delete frozen axiom | 2–4 |

Near-term total: approximately **10–23 prompts**, with the phase–parameter theorem
the main uncertainty. This is still much shorter and more relevant than continuing
the renormalization/straightening detour.

Prompt 24's tube-fiber task is suspended. Its work remains valid but is not on the
active path to this frontier.
