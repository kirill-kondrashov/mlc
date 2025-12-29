import Mlc.MainConjecture
import Lean

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let name := ``MLC.MLC_Conjecture
  let axioms ← Lean.collectAxioms name
  if axioms.contains ``sorryAx then
    throwError "❌ The proof of '{name}' relies on 'sorry'!"
  else
    logInfo s!"✅ The proof of '{name}' is free of 'sorry'."
    logInfo s!"All axioms used: {axioms.toList}"
