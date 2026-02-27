# Plan: Frontier Closure and Cleanup

---
**Status:** `██████████` **100%** | **Relevance:** ⭐⭐⭐⭐☆ | **State:** `DONE`
**Scope:** integration, verification, and anti-regression guardrails
**Effort Left:** **0h**
**Last Updated:** 2026-02-27
---

## Objective

Keep the frontier tight while axioms are removed:

- enforce only the two known target axioms until each is eliminated,
- keep README and verification script aligned with current policy,
- prevent stale/stuck plan drift.

## Current Reality

- `make check` failure is already narrowed to exactly two target axioms.
- Previous temporary "allowed frontier" relaxations were reverted.
- Plan folder has been compacted to active execution plans.
- `scripts/verify_output.sh` re-run and matching README behavior confirmed.

## Work Plan

1. After each axiom-elimination patch set, run:
   - `lake build Mlc.MainConjecture`
   - `make check`
2. If frontier changes, update:
   - `scripts/verify_output.sh`
   - `README.md` (short, explicit frontier note)
3. Keep umbrella + active plans in sync (progress, effort left, dead-end guard).
4. Remove obsolete helper aliases/comments once each axiom disappears.

## Progress Checklist

- [x] Frontier constrained to two explicit target axioms.
- [x] Temporary frontier relaxations removed.
- [x] Stuck plan files removed.
- [x] README and script wording rechecked after latest elimination iteration.
- [x] Iteration logs and dead-end guard updated across active plans.
- [x] Final classification complete: all plans now `DONE` or `STUCK`.

## Risks / Mitigations

- Risk: docs/script drift from real `make check` output.
  Mitigation: treat `make check` output as source of truth and patch docs/script
  in the same commit window.
- Risk: stale plan percentages after rapid edits.
  Mitigation: update this and umbrella status at end of each iteration.

## Done Criteria

- Verification flow reproducible:
  `make check` + `scripts/verify_output.sh` match documented frontier state.
- Plan set contains no stale active items outside `DONE`/`STUCK`.
