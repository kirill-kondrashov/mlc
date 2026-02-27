# Plan: Axiom 2 Nonreal Transport Inventory (v2)

---
**Status:** `████░░░░░░` **40%** | **Relevance:** ⭐⭐⭐⭐⭐ | **State:** `ACTIVE`
**Axiom Target:** `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`
**Effort Left:** **6-10h** (roughly 150-320 Lean LOC)
**Last Updated:** 2026-02-27
---

## Objective

Close `GreenFunctionStrictMonoAlongNonRealDirectionsTwoSeam` by adding missing
nonreal-direction transport lemmas and replacing residual axiom-seeded seams.

## Work Plan

1. Inventory existing lemmas usable for nonreal unit directions.
2. Add minimal transport lemmas to bridge from existing full-ray identities.
3. Prove the residual nonreal seam constructively.
4. Remove nonreal axiom-seed entry points from full seam assembly.
5. Re-run targeted build and `make check`.

## Progress Checklist

- [x] Real-direction branch is complete.
- [x] Residual nonreal seam is isolated.
- [ ] Nonreal transport lemma inventory completed in-code comments/notes.
- [ ] Residual seam closed constructively.
- [ ] `make check` no longer lists
      `MLC.Quadratic.green_function_strictMono_along_ray_basin_seam`.
