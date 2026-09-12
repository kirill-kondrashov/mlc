import Mlc.UniformGeometricRoot
import Mlc.UniformGeometricVertexControl
import Mlc.TrappingRegionObstruction
import Mlc.FiniteTrappingRegions
import Lean

open Lean Meta

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[
    { module := `Mlc.UniformGeometricRoot },
    { module := `Mlc.UniformGeometricVertexControl },
    { module := `Mlc.TrappingRegionObstruction },
    { module := `Mlc.FiniteTrappingRegions }
  ] {}
  let names : Array Name := #[
    ``MLC.UniformGeometry.dist_affine_combinations_le,
    ``MLC.UniformGeometry.parameterSquare_near_outer_zero,
    ``MLC.UniformGeometry.exists_continuous_retraction,
    ``MLC.UniformGeometry.mandelbrot_locallyConnected_of_squareTower,
    ``MLC.UniformGeometry.categorical_mlc_of_squareTower,
    ``MLC.UniformGeometry.exists_squareTower_strongDeformation,
    ``MLC.CertifiedTrapping.not_innerDensity,
    ``MLC.FiniteTrapping.TrappingCertificate.parameterBox_subset_interior_mandelbrot,
    ``MLC.FiniteTrapping.periodTwoCertificate_hasMargin,
    ``MLC.FiniteTrapping.periodTwoParameterBox_subset_mandelbrot,
    ``MLC.FiniteTrapping.periodTwoParameterBox_subset_interior_mandelbrot
  ]
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  let audit : MetaM (String × Array (Name × Array Name)) := do
    let theoremInfo ← getConstInfo
      ``MLC.UniformGeometry.mandelbrot_locallyConnected_of_squareTower
    let theoremType ← ppExpr theoremInfo.type
    let results ← names.mapM fun name => do
      return (name, ← Lean.collectAxioms name)
    return (theoremType.pretty, results)
  let context : Core.Context :=
    { fileName := "<check_uniform_program>", fileMap := default }
  let state : Core.State := { env := env }
  let (((theoremType, results), _), _) ←
    (audit.run).run context state |>.toIO
      (fun _ => IO.userError "Could not audit the uniform geometry declarations.")
  IO.println "Conditional geometric theorem:"
  IO.println theoremType
  IO.println "Existence of an OrbitRetractionTower remains an explicit hypothesis."
  let mut violation := false
  for (name, axioms) in results do
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    if unexpected.isEmpty then
      IO.println s!"Foundation-only: {name}"
    else
      violation := true
      IO.println s!"Unexpected axioms in {name}: {unexpected.toList}"
  return if violation then 1 else 0
