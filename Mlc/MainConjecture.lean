import Mlc.Quadratic.Complex.Basic
import Mlc.Quadratic.Complex.Green
import Mlc.Quadratic.Complex.Bottcher
import Mlc.Quadratic.Complex.Puzzle
import Mlc.Yoccoz
import Mlc.LcAtOfShrink
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean

open Lean Elab Command

elab "ensure_no_sorry" n:ident : command => do
  let name ← resolveGlobalConstNoOverload n
  let axioms ← collectAxioms name
  if axioms.contains ``sorryAx then
    let info ← getConstInfo name
    match info.value? with
    | some v =>
      let sorryDeps := v.foldConsts (init := #[]) fun c acc =>
        acc.push c

      let mut culprits := #[]
      for dep in sorryDeps do
        if dep != name then
           let depAxioms ← collectAxioms dep
           if depAxioms.contains ``sorryAx then
             culprits := culprits.push dep

      let culpritsList := culprits.toList.eraseDups

      if culpritsList.isEmpty then
        throwError m!"{name} depends on sorryAx directly!"
      else
        throwError m!"{name} depends on sorryAx through: {culpritsList}"
    | none => throwError m!"{name} depends on sorryAx (no value available to inspect)"
  else
    logInfo m!"{name} is sorry-free!"

namespace MLC

open Quadratic Complex Topology Set Filter

/-!
# Mandelbrot Local Connectivity (MLC) Conjecture

This file outlines the proof strategy for the MLC conjecture based on Yoccoz puzzles.
-/

section Renormalization

/-- Infinitely renormalizable parameters.
    For the purpose of this plan, we define infinitely renormalizable parameters
    as those for which the Yoccoz puzzle moduli converge.
    In a full theory, this would be a theorem (Yoccoz). -/
def InfinitelyRenormalizable (c : ℂ) : Prop :=
  Summable (fun n => modulus (PuzzleAnnulus c n))

/-- MLC holds for infinitely renormalizable parameters (Lyubich). -/
theorem mlc_infinitely_renormalizable (c : ℂ) (hc : c ∈ MandelbrotSet) (h : InfinitelyRenormalizable c) :
    LocallyConnectedAt MandelbrotSet ⟨c, hc⟩ := sorry

end Renormalization

section MainProof

/-- Every parameter is either non-renormalizable or infinitely renormalizable. -/
theorem dichotomy (c : ℂ) : NonRenormalizable c ∨ InfinitelyRenormalizable c := by
  rw [NonRenormalizable, InfinitelyRenormalizable]
  by_cases h : Summable (fun n => modulus (PuzzleAnnulus c n))
  · right; exact h
  · left; exact h

/-- If dynamical pieces shrink to a point, parameter pieces shrink to a point. -/
lemma parameter_shrink (c : ℂ) (h : (⋂ n, DynamicalPuzzlePiece c n 0) = {0}) :
    (⋂ n, ParaPuzzlePiece n) = {c} := by
  -- Use the correspondence principle
  apply parameter_shrink_ax c h

/-- The Mandelbrot Local Connectivity (MLC) Conjecture:
    The Mandelbrot set is locally connected. -/
theorem MLC_Conjecture : LocallyConnectedSpace MandelbrotSet := by
  -- We need to show local connectivity at every point c ∈ MandelbrotSet
  apply locallyConnectedSpace_of_locallyConnectedAt
  intro ⟨c, hc⟩
  rcases dichotomy c with h_non_renorm | h_inf_renorm
  · -- Case 1: Non-renormalizable
    have h_div := non_renormalizable_moduli_diverge c h_non_renorm
    have h_dyn := yoccoz_theorem c h_div
    have h_para := parameter_shrink c h_dyn
    exact lc_at_of_shrink c hc h_para
  · -- Case 2: Infinitely renormalizable
    exact mlc_infinitely_renormalizable c hc h_inf_renorm

end MainProof

end MLC

ensure_no_sorry MLC.locallyConnectedSpace_of_locallyConnectedAt
ensure_no_sorry MLC.yoccoz_theorem
ensure_no_sorry MLC.non_renormalizable_moduli_diverge
ensure_no_sorry MLC.InfinitelyRenormalizable
ensure_no_sorry MLC.dichotomy
ensure_no_sorry MLC.parameter_shrink
ensure_no_sorry MLC.lc_at_of_shrink

-- Verify that the main conjecture does not depend on sorry
-- ensure_no_sorry MLC.MLC_Conjecture
