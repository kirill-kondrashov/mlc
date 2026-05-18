import Mlc.MainConjecture
import Lean

open Lean Meta

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mlc.MainConjecture }] {}
  
  let name := ``MLC.mlc_conjecture
  
  let coreContext : Core.Context := { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }
  
  let metaM : MetaM (Array Name) := Lean.collectAxioms name
  let expectedAxioms : List Name :=
     [``Quot.sound, ``propext, ``Classical.choice,
      ``MLC.Quadratic.external_ray_map_exists]
  
  try
    let ((axioms, _), _) ← (metaM.run).run coreContext coreState |>.toIO (fun _ => IO.userError "Axiom check failed")
    let axiomsList := axioms.toList
    let hasSorry := axioms.contains ``sorryAx
    let unexpected := axiomsList.filter (fun ax => !(expectedAxioms.contains ax))
    let missing := expectedAxioms.filter (fun ax => !(axiomsList.contains ax))
    
    if hasSorry then
      IO.println s!"❌ The proof of '{name}' relies on 'sorry'!"
    else
      IO.println s!"✅ The proof of '{name}' is free of 'sorry'."
    
    IO.println "All axioms used:"
    for ax in axiomsList do
      IO.println s!"- {ax}"
    
    if hasSorry then
      return (1 : UInt32)
    else if !unexpected.isEmpty || !missing.isEmpty then
      IO.println "❌ Axiom frontier violation for `MLC.mlc_conjecture`."
      if !unexpected.isEmpty then
        IO.println "Unexpected axioms:"
        for ax in unexpected do
          IO.println s!"- {ax}"
      if !missing.isEmpty then
        IO.println "Missing required axioms:"
        for ax in missing do
          IO.println s!"- {ax}"
      return (1 : UInt32)
    else
      return (0 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
