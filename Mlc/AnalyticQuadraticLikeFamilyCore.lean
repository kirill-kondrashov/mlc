import Molecule.BMol
import Mlc.GenuineBMol
import Mathlib.Analysis.Analytic.Basic

/-!
# Analytic quadratic-like family core

This module implements a deliberately incomplete core for analytic quadratic-like
family data over a parameter domain. It records only the scoped total-source /
total-target sets, their fiberwise agreement with `GenuineBMol`, and joint
analyticity on the actual total source.

It intentionally omits the source text's stronger tube fiber-bundle /
local-triviality structure as well as all later theorem hypotheses such as
properness, unfolding, equipment, holomorphic motion, tubing, and straightening.
-/

open Set
open Complex

namespace Molecule

/--
A minimal analytic quadratic-like family core over a parameter domain.

This is only the scoped analytic core used for later development. It does **not**
claim to be the full source-defined quadratic-like family object: in particular it
omits tube fiber-bundle / local-triviality data and all later proper / unfolded /
equipped hypotheses.
-/
structure AnalyticQuadraticLikeFamilyCore where
  parameterSet : Set ℂ
  isOpen_parameterSet : IsOpen parameterSet
  fiber : parameterSet → GenuineBMol
  totalU : Set (ℂ × ℂ)
  totalV : Set (ℂ × ℂ)
  scoped_totalU : totalU ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
  scoped_totalV : totalV ⊆ parameterSet ×ˢ (Set.univ : Set ℂ)
  isOpen_totalU : IsOpen totalU
  isOpen_totalV : IsOpen totalV
  sectionU_eq (c : parameterSet) : {z : ℂ | (c.1, z) ∈ totalU} = (fiber c : BMol).U
  sectionV_eq (c : parameterSet) : {z : ℂ | (c.1, z) ∈ totalV} = (fiber c : BMol).V
  eval : ℂ × ℂ → ℂ
  eval_agrees (c : parameterSet) {z : ℂ} (hz : (c.1, z) ∈ totalU) :
    eval (c.1, z) = (fiber c : BMol).f z
  analyticOn_totalU : AnalyticOn ℂ eval totalU

namespace AnalyticQuadraticLikeFamilyCore

/-- The source section of the total domain over a parameter value. -/
def sectionU (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) : Set ℂ :=
  {z : ℂ | (c.1, z) ∈ F.totalU}

/-- The target section of the total codomain over a parameter value. -/
def sectionV (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) : Set ℂ :=
  {z : ℂ | (c.1, z) ∈ F.totalV}

@[simp] lemma mem_sectionU_iff (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet)
    (z : ℂ) : z ∈ F.sectionU c ↔ (c.1, z) ∈ F.totalU :=
  Iff.rfl

@[simp] lemma mem_sectionV_iff (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet)
    (z : ℂ) : z ∈ F.sectionV c ↔ (c.1, z) ∈ F.totalV :=
  Iff.rfl

lemma sectionU_eq_fiberU (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) :
    F.sectionU c = (F.fiber c : BMol).U :=
  F.sectionU_eq c

lemma sectionV_eq_fiberV (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) :
    F.sectionV c = (F.fiber c : BMol).V :=
  F.sectionV_eq c

lemma eval_agrees_section (F : AnalyticQuadraticLikeFamilyCore) (c : F.parameterSet) {z : ℂ}
    (hz : z ∈ F.sectionU c) : F.eval (c.1, z) = (F.fiber c : BMol).f z :=
  F.eval_agrees c hz

lemma fst_mem_parameterSet_of_mem_totalU (F : AnalyticQuadraticLikeFamilyCore) {p : ℂ × ℂ}
    (hp : p ∈ F.totalU) : p.1 ∈ F.parameterSet :=
  (F.scoped_totalU hp).1

lemma fst_mem_parameterSet_of_mem_totalV (F : AnalyticQuadraticLikeFamilyCore) {p : ℂ × ℂ}
    (hp : p ∈ F.totalV) : p.1 ∈ F.parameterSet :=
  (F.scoped_totalV hp).1

end AnalyticQuadraticLikeFamilyCore

end Molecule
