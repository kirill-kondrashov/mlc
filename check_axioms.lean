import Mlc.Core
import Mlc.GreenSublevelIntersectionCounterexample
import Mlc.Literature.ModelAudit
import Lean

open Lean Meta

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `Mlc.Core },
    { module := `Mlc.GreenSublevelIntersectionCounterexample },
    { module := `Mlc.Literature.ModelAudit }
  ] {}

  let name := ``MLC.mlc_conjecture
  let categoricalName := ``MLC.Categorical.categorical_mlc_conjecture
  let negationName := ``MLC.not_greenSublevelIntersectionCategoricalData
  let expectedAxioms : List Name :=
    [``Quot.sound, ``propext, ``Classical.choice]
  let literatureNames := #[
    ``MLC.Literature.localConnectivity_of_compact_parameterPieces,
    ``MLC.Categorical.Mandelbrot.innerOrbitSet_eq_set_of_two_le,
    ``MLC.Literature.relativePeriodProduct_periodDoubling,
    ``MLC.Literature.ModelAudit.not_finitelyRenormalizable_in_frozenModel,
    ``MLC.Literature.ModelAudit.not_nonempty_satelliteAPrioriCertificate
  ]

  let coreContext : Core.Context :=
    { fileName := "<check_axioms>", fileMap := default }
  let coreState : Core.State := { env := env }

  let rootMetaM : MetaM (Array Name × Array Name) := do
    let rootAxioms ← Lean.collectAxioms name
    let categoricalAxioms ← Lean.collectAxioms categoricalName
    pure (rootAxioms, categoricalAxioms)
  let negationMetaM : MetaM (Array Name) :=
    Lean.collectAxioms negationName
  let literatureMetaM : MetaM (Array (Name × Array Name)) := do
    let mut results := #[]
    for declaration in literatureNames do
      results := results.push (declaration, ← Lean.collectAxioms declaration)
    pure results

  try
    let (((axioms, categoricalAxioms), _), _) ←
      (rootMetaM.run).run coreContext coreState |>.toIO
        (fun _ => IO.userError "Axiom check failed")
    let ((negationAxioms, _), _) ←
      (negationMetaM.run).run coreContext coreState |>.toIO
        (fun _ => IO.userError "Negation axiom check failed")
    let ((literatureAxioms, _), _) ←
      (literatureMetaM.run).run coreContext coreState |>.toIO
        (fun _ => IO.userError "Literature axiom check failed")

    let axiomsList := axioms.toList
    let categoricalAxiomsList := categoricalAxioms.toList
    let negationAxiomsList := negationAxioms.toList
    let unexpected (actual : List Name) :=
      actual.filter (fun ax => !(expectedAxioms.contains ax))
    let missing (actual : List Name) :=
      expectedAxioms.filter (fun ax => !(actual.contains ax))
    let sameAxiomSet :=
      axiomsList.all (fun ax => categoricalAxioms.contains ax) &&
        categoricalAxiomsList.all (fun ax => axioms.contains ax)
    let rootViolation :=
      !(unexpected axiomsList).isEmpty ||
        !(missing axiomsList).isEmpty ||
        !(unexpected categoricalAxiomsList).isEmpty ||
        !(missing categoricalAxiomsList).isEmpty ||
        !sameAxiomSet ||
        axioms.contains ``sorryAx ||
        categoricalAxioms.contains ``sorryAx
    let negationViolation :=
      !(unexpected negationAxiomsList).isEmpty ||
        !(missing negationAxiomsList).isEmpty ||
        negationAxioms.contains ``sorryAx

    if axioms.contains ``sorryAx then
      IO.println s!"❌ The proof of '{name}' relies on 'sorry'!"
    else
      IO.println s!"✅ The proof of '{name}' is free of 'sorry'."

    IO.println "All axioms used:"
    for ax in axiomsList do
      IO.println s!"- {ax}"

    IO.println
      "The root theorems require the explicit `MLC.RootInput` hypothesis."
    if negationAxioms.contains ``sorryAx then
      IO.println s!"❌ The proof of '{negationName}' relies on 'sorry'!"
    else
      IO.println s!"✅ The proof of '{negationName}' is free of 'sorry'."

    let mut literatureViolation := false
    for (declaration, declarationAxioms) in literatureAxioms do
      let forbidden := unexpected declarationAxioms.toList
      if !forbidden.isEmpty then
        literatureViolation := true
        IO.println s!"❌ Unexpected axioms for '{declaration}': {forbidden}"
    if !literatureViolation then
      IO.println "✅ Literature foundations and frozen-model audit use only permitted axioms."

    if rootViolation || negationViolation || literatureViolation then
      IO.println "❌ Axiom frontier violation for `MLC.mlc_conjecture`."
      for ax in unexpected axiomsList do
        IO.println s!"- Unexpected axiom: {ax}"
      for ax in missing axiomsList do
        IO.println s!"- Missing required axiom: {ax}"
      for ax in unexpected categoricalAxiomsList do
        IO.println s!"- Unexpected categorical-root axiom: {ax}"
      for ax in missing categoricalAxiomsList do
        IO.println s!"- Missing categorical-root axiom: {ax}"
      for ax in unexpected negationAxiomsList do
        IO.println s!"- Unexpected negation axiom: {ax}"
      for ax in missing negationAxiomsList do
        IO.println s!"- Missing negation axiom: {ax}"
      if !sameAxiomSet then
        IO.println "❌ The categorical root and compatibility root use different axiom sets."
      return (1 : UInt32)
    else
      return (0 : UInt32)
  catch e =>
    IO.println s!"Error: {e}"
    return (1 : UInt32)
