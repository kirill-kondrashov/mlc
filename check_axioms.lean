import Mlc.Core
import Lean

open Lean Meta

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mlc.Core }] {}

  let rootName := ``MLC.mlc_conjecture
  let categoricalName := ``MLC.Categorical.categorical_mlc_conjecture
  let expectedAxioms : List Name :=
    [``Quot.sound, ``propext, ``Classical.choice]
  let coreDeclarations := #[
    ``MLC.Problem44VirtualMoleculeData.coverage,
    ``MLC.mlc_of_problem43_problem44,
    ``MLC.RootInput.locallyConnectedSpace
  ]

  let coreContext : Core.Context :=
    { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }

  let audit : MetaM (Array Name × Array Name × Array (Name × Array Name)) := do
    let rootAxioms ← Lean.collectAxioms rootName
    let categoricalAxioms ← Lean.collectAxioms categoricalName
    let mut checked := #[]
    for declaration in coreDeclarations do
      checked := checked.push (declaration, ← Lean.collectAxioms declaration)
    for (declaration, info) in env.constants.toList do
      if (`MLC.Research).isPrefixOf declaration then
        if info matches .thmInfo _ then
          checked := checked.push (declaration, ← Lean.collectAxioms declaration)
    pure (rootAxioms, categoricalAxioms, checked)

  try
    let (((rootAxioms, categoricalAxioms, checkedAxioms), _), _) ←
      (audit.run).run coreContext coreState |>.toIO
        (fun _ => IO.userError "Axiom check failed")

    let unexpected (actual : List Name) :=
      actual.filter (fun ax => !(expectedAxioms.contains ax))
    let missing (actual : List Name) :=
      expectedAxioms.filter (fun ax => !(actual.contains ax))
    let sameAxiomSet :=
      rootAxioms.toList.all (fun ax => categoricalAxioms.contains ax) &&
        categoricalAxioms.toList.all (fun ax => rootAxioms.contains ax)
    let rootViolation :=
      !(unexpected rootAxioms.toList).isEmpty ||
        !(missing rootAxioms.toList).isEmpty ||
        !(unexpected categoricalAxioms.toList).isEmpty ||
        !(missing categoricalAxioms.toList).isEmpty ||
        !sameAxiomSet ||
        rootAxioms.contains ``sorryAx ||
        categoricalAxioms.contains ``sorryAx
    let checkedViolation :=
      checkedAxioms.any fun (_, axioms) =>
        !(unexpected axioms.toList).isEmpty || axioms.contains ``sorryAx

    if rootAxioms.contains ``sorryAx then
      IO.println s!"❌ The proof of '{rootName}' relies on 'sorry'!"
    else
      IO.println s!"✅ The proof of '{rootName}' is free of 'sorry'."

    IO.println "All axioms used:"
    for ax in rootAxioms do
      IO.println s!"- {ax}"

    IO.println "Conditional root: Dudko Problems 4.3 and 4.4 are explicit root inputs."
    if checkedViolation then
      IO.println "❌ A reachable Lean declaration uses an unexpected axiom."
      for (declaration, axioms) in checkedAxioms do
        for ax in unexpected axioms.toList do
          IO.println s!"- Unexpected axiom in '{declaration}': {ax}"
    else
      IO.println "✅ Every reachable research theorem uses only ground axioms."

    if rootViolation || checkedViolation then
      IO.println "❌ Axiom frontier violation for `MLC.mlc_conjecture`."
      for ax in unexpected rootAxioms.toList do
        IO.println s!"- Unexpected root axiom: {ax}"
      for ax in missing rootAxioms.toList do
        IO.println s!"- Missing root axiom: {ax}"
      if !sameAxiomSet then
        IO.println "❌ The categorical and compatibility roots use different axiom sets."
      return (1 : UInt32)
    else
      return (0 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
