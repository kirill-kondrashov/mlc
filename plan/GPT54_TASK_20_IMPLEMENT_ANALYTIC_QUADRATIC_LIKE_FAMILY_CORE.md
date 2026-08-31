# GPT-5.4 Worker Task 20: Implement the analytic quadratic-like family core

**Repository:** `/home/kir/pers/mlc`
**Mode:** small Lean implementation
**New file:** `Mlc/AnalyticQuadraticLikeFamilyCore.lean`
**Result file:** `plan/GPT54_RESULT_20_IMPLEMENT_ANALYTIC_QUADRATIC_LIKE_FAMILY_CORE.md`

## Safety and scope

Read Results 18–19 and Supervisor Review 19. Preserve unrelated working-tree
changes. Do not edit vendored dependencies and do not commit. Introduce no
`axiom`, `sorry`, or `admit`.

This task implements a deliberately incomplete **core**, not the complete
source-defined quadratic-like family. Do not add or claim tube fiber-bundle
triviality, family properness, unfolding, equipment, holomorphic motion, tubing,
straightening, or connectedness theorems.

## Required implementation

Create `Mlc/AnalyticQuadraticLikeFamilyCore.lean` in namespace `Molecule` with a
structure named exactly:

```lean
AnalyticQuadraticLikeFamilyCore
```

Use the compile-tested primitive fields from Result 18:

- `parameterSet : Set ℂ` and `isOpen_parameterSet`;
- subtype-indexed `fiber : parameterSet → GenuineBMol`;
- `totalU totalV : Set (ℂ × ℂ)`;
- scoping laws into `parameterSet ×ˢ univ`;
- openness of both total spaces;
- section-equality laws tying total spaces to fiber `U` and `V`;
- global `eval : ℂ × ℂ → ℂ`;
- evaluation agreement on the total source;
- `AnalyticOn ℂ eval totalU`.

The module and structure docstrings must explicitly say this is a core and omits
the source's tube fiber-bundle/local-triviality data and all later theorem
hypotheses.

## Derived namespace API

Outside the structure, in namespace `AnalyticQuadraticLikeFamilyCore`, define:

- `sectionU`, `sectionV`;
- `[simp] mem_sectionU_iff`, `[simp] mem_sectionV_iff`;
- section equality lemmas exposing the corresponding fiber domains;
- evaluation agreement using membership in `sectionU`;
- first-coordinate membership lemmas for points of `totalU` and `totalV`.

Do not store derived sections or tautological membership facts as structure fields.

Add `import Mlc.AnalyticQuadraticLikeFamilyCore` to `Mlc.lean` without unrelated
reordering.

## Verification

Run:

```bash
lake env lean Mlc/AnalyticQuadraticLikeFamilyCore.lean
lake build
```

Search the changed Lean files for `axiom`, `sorry`, and `admit`; inspect the exact
diff and complete `git status --short`.

## Result report

Write the authorized result artifact with declarations, deviations, verification
outcomes, changed files, full status, and confirmation that no commit was made.
Only the new module, `Mlc.lean`, and the Result 20 report are authorized changes.
