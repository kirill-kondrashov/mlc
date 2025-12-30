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
