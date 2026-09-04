import Mlc.Core
import Lean

open Lean Meta

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mlc.Core }] {}
  
  let name := ``MLC.mlc_conjecture
  let categoricalName := ``MLC.Categorical.categorical_mlc_conjecture
  
  let coreContext : Core.Context := { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }
  
  let metaM : MetaM (Array Name × Array Name) := do
    let rootAxioms ← Lean.collectAxioms name
    let categoricalAxioms ← Lean.collectAxioms categoricalName
    pure (rootAxioms, categoricalAxioms)
  let expectedAxioms : List Name :=
   [``Quot.sound, ``propext, ``Classical.choice,
    ``MLC.green_sublevel_intersection_categorical,
    ``MLC.residualOpenVirtualNearMoleculeAxiom]
  
  try
    let (((axioms, categoricalAxioms), _), _) ←
      (metaM.run).run coreContext coreState |>.toIO (fun _ => IO.userError "Axiom check failed")
    let axiomsList := axioms.toList
    let categoricalAxiomsList := categoricalAxioms.toList
    let hasSorry := axioms.contains ``sorryAx
    let unexpected := axiomsList.filter (fun ax => !(expectedAxioms.contains ax))
    let missing := expectedAxioms.filter (fun ax => !(axiomsList.contains ax))
    let categoricalHasSorry := categoricalAxioms.contains ``sorryAx
    let categoricalUnexpected :=
      categoricalAxiomsList.filter (fun ax => !(expectedAxioms.contains ax))
    let categoricalMissing :=
      expectedAxioms.filter (fun ax => !(categoricalAxiomsList.contains ax))
    let sameAxiomSet :=
      axiomsList.all (fun ax => categoricalAxioms.contains ax) &&
        categoricalAxiomsList.all (fun ax => axioms.contains ax)
    
    if hasSorry then
      IO.println s!"❌ The proof of '{name}' relies on 'sorry'!"
    else
      IO.println s!"✅ The proof of '{name}' is free of 'sorry'."
    
    IO.println "All axioms used:"
    for ax in axiomsList do
      IO.println s!"- {ax}"
    
    if hasSorry || categoricalHasSorry then
      return (1 : UInt32)
    else if !unexpected.isEmpty || !missing.isEmpty ||
        !categoricalUnexpected.isEmpty || !categoricalMissing.isEmpty || !sameAxiomSet then
      IO.println "❌ Axiom frontier violation for `MLC.mlc_conjecture`."
      if !unexpected.isEmpty then
        IO.println "Unexpected axioms:"
        for ax in unexpected do
          IO.println s!"- {ax}"
      if !missing.isEmpty then
        IO.println "Missing required axioms:"
        for ax in missing do
          IO.println s!"- {ax}"
      if !categoricalUnexpected.isEmpty then
        IO.println "Unexpected categorical-root axioms:"
        for ax in categoricalUnexpected do
          IO.println s!"- {ax}"
      if !categoricalMissing.isEmpty then
        IO.println "Missing categorical-root axioms:"
        for ax in categoricalMissing do
          IO.println s!"- {ax}"
      if !sameAxiomSet then
        IO.println "❌ The categorical root and compatibility root use different axiom sets."
      return (1 : UInt32)
    else
      return (0 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
