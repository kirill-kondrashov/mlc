import Mlc
import Lean

/-! Export actual constants in elaborated types and proof terms.
The Python renderer supplies source positions and visual presentation. -/

open Lean

def declarationKind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "structure"
  | _ => "def"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Mlc }] {}
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if (`MLC).isPrefixOf name then
      let deps := info.getUsedConstantsAsSet.toArray.map (fun n => Json.str n.toString)
      rows := rows.push <| Json.mkObj [
        ("name", Json.str name.toString),
        ("kind", Json.str (declarationKind info)),
        ("dependencies", Json.arr deps)]
  IO.println (Json.arr rows).compress
