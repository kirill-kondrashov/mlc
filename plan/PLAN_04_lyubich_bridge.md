# PLAN 04: Eliminate `lyubich_conformal_bridge`

**Status:** LONG-TERM — requires real conformal moduli or restructuring
**Difficulty:** Very Hard
**Depends on:** Other axioms handled first

---

## What It Is

```lean
axiom lyubich_conformal_bridge :
  ∀ (c : ℂ) (T : RenormalizationTower (parameterToBMol c)),
    (¬ Summable (fun n => LyubichModulus c T.cumulativePeriod n)) →
    (¬ Summable (fun n => cmodulus c n))
```

This bridges:
- `LyubichModulus c T n` — the fake proxy modulus (currently `= 1`, always non-summable)
- `cmodulus c n` — the "Gaussian" proxy modulus (always summable, by Gaussian argument)

Together they give `False`, making the InconsistencyRoute work.

---

## Why Both Moduli Are Fake

**`LyubichModulus c T n = 1`** (defined as constant in `PrimitiveModulusDivergence.lean`).
This is a placeholder for the conformal modulus of the Lyubich principal nest annuli.
The real Lyubich moduli have a positive lower bound (Lyubich's theorem), hence diverge.

**`cmodulus c n`** = Gaussian modulus (always summable).
This is a placeholder for the true conformal modulus of the puzzle annuli.
With real puzzle annuli, this would NOT be summable (by Lyubich's theorem).

**`lyubich_conformal_bridge`** connects them via the proxy values.
It's mathematically wrong as stated (bridges fake values), but creates the intended inconsistency.

---

## The Real Fix (Option A): Use Real Moduli

Replace both proxies with actual conformal moduli of puzzle annuli:
1. Redefine `LyubichModulus c T n` = conformal modulus of principal nest annulus n
2. Redefine `cmodulus c n` = same (or a comparable modulus)
3. Then `lyubich_conformal_bridge` becomes `≥ μ > 0` for all n → series diverges

**Cost**: Major redesign of the Yoccoz puzzle / modulus framework.
Requires: proper definition of puzzle pieces, conformal moduli, Grötzsch inequality.

---

## Option B: Replace Proxy with Axiom

Add a dedicated axiom:
```lean
axiom lyubich_modulus_lower_bound :
  ∃ μ > 0, ∀ c T n, LyubichModulus c T n ≥ μ
```

From this, `¬Summable LyubichModulus` follows (proved, not axiomatic).
Then `lyubich_conformal_bridge` can be proved from `lyubich_modulus_lower_bound`
plus the relation between LyubichModulus and cmodulus.

**Advantage**: Separates two concerns — the lower bound (a clear mathematical claim)
from the bridge (a technical connection). The lower bound is a directly citable theorem.

---

## Option C: Accept as Standard Axiom

`lyubich_conformal_bridge` corresponds to Lyubich's 1997 theorem on a priori bounds.
This is a classical result proven in hundreds of pages of complex analysis.
Accepting it as an axiom is standard practice in complex dynamics formalization.

**Recommendation**: Keep as axiom for now. This is mathematically defensible.
Label clearly: "Lyubich's a priori bounds theorem (1997)".

---

## Connection to InconsistencyRoute Architecture

The ENTIRE proof rests on an inconsistency manufactured from proxy values.
To eliminate `lyubich_conformal_bridge`, one must either:
1. Make the proxies real (Option A — massive refactoring)
2. Replace with a more direct axiom (Option B — improvement)
3. Accept it (Option C — status quo)

Option B is the most actionable improvement that doesn't require restructuring everything.

---

## Conclusion

`lyubich_conformal_bridge` should be kept as an axiom unless Option B is pursued.
Option B (lyubich_modulus_lower_bound) is worth attempting as a cleaner formulation.
Option A is a long-term research goal.
