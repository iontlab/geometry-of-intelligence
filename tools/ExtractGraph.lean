import ILab.RQ001.FourStateQuotient
import ILab.RQ001.CapabilityOrder
import ILab.RQ001.SymmetryObstruction
import ILab.RQ001.TransformationSufficientQuotient

open Lean in
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.map Prod.fst).filter (fun n => `ILab.RQ001 |>.isPrefixOf n)
  let names := names.toArray.qsort (fun a b => a.toString < b.toString)
  let mut nodes : Array Json := #[]
  for name in names do
    let info := env.find? name |>.get!
    match info with
    | .axiomInfo _ => throwError "Project axiom: {name}"
    | _ => pure ()
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      throwError "Admitted expression: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom dependency {ax} in {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo val => match val.hints with | .abbrev => "abbreviation" | _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient primitive"
    let mut deps := info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
    let localDeps := (deps.filter (fun n => `ILab.RQ001 |>.isPrefixOf n)).toList.eraseDups.toArray.qsort (fun a b => a.toString < b.toString)
    let signature ← Elab.Command.liftTermElabM <| Meta.ppExpr info.type
    let mod := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "unknown"
    nodes := nodes.push <| Json.mkObj [
      ("id", toJson name.toString), ("kind", toJson kind),
      ("module", toJson mod), ("signature", toJson signature.pretty),
      ("dependencies", toJson (localDeps.map Name.toString)),
      ("axioms", toJson ((axioms.map Name.toString).qsort (· < ·)))]
  IO.FS.writeFile "docs/formalization/rq001/compiled.json" (Json.pretty (toJson nodes))
  logInfo m!"PASS: extracted and audited {nodes.size} project declarations from compiled Lean types and values."


