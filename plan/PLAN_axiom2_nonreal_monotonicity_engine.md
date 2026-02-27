# Plan: Eliminate `green_function_strictMono_along_ray_basin_seam` via Nonreal Monotonicity Engine

---
**Status:** `█████░░░░░` **45%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`
**Effort Left:** **6-10h** (roughly 160-300 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Constructively prove the residual seam:

- `GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam`

then eliminate:

- `green_function_strictMono_along_nonRealDirections_two_axiom_seed`
- `green_function_strictMono_along_ray_basin_two_axiom_seed`

## Why This Plan

- Real-direction monotonicity (`u = ±1`) is complete.
- Residual debt is isolated to non-real unit directions.

## Work Plan

1. Add non-real direction normalization lemmas (`u ≠ ±1`, `‖u‖ = 1`).
2. Build monotonicity transport lemmas along rays using existing Green
   functional identities.
3. Prove the non-real seam constructively.
4. Replace mixed-seed assembly with fully constructive seam assembly.
5. Re-run `lake build Mlc.Quadratic.Complex.Bottcher.GreenFunctionRayInversion`
   and `make check`.

## Progress Checklist

- [x] Real-direction seam is constructive.
- [x] Residual seam isolated behind one interface.
- [ ] Non-real-direction transport lemmas completed.
- [ ] Residual seam proven without axioms.
- [ ] `make check` no longer lists
      `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`.

## Dead-End Guard

- Do not reopen real-direction lemmas unless a regression appears.
- Keep edits concentrated in non-real seam and assembly layer.

## Done Criteria

- No active dependency path to `green_function_strictMono_along_ray_basin_seam`.
- `make check` frontier drops Axiom 2.
