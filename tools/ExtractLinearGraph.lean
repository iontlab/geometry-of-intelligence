import ILab.LinearAlgebra
import Lean

/-!
Adapted from iLab tools/ExtractLearningGraph.lean and tools/ExtractGraph.lean.
Edges are direct constant references in compiled types and values. A bounded,
explicit library selection exposes relevant Mathlib foundations without either
transitive shortcut edges or a complete low-level Mathlib graph.
-/

open Lean in
run_cmd do
  let env ← getEnv
  let localNames := (env.constants.toList.map Prod.fst).filter
    (fun n => `ILab.LinearAlgebra |>.isPrefixOf n)
  let library : Array Name := #[
    `Field, `Module, `Module.Free, `Module.Finite, `Module.finrank, `Module.rank,
    `Module.Basis, `Module.Basis.linearIndependent, `Module.Basis.span_eq,
    `Module.Basis.mk, `Module.finBasis, `LinearIndependent, `Submodule,
    `Submodule.span, `LinearMap, `LinearMap.ker, `LinearMap.range,
    `LinearMap.quotKerEquivRange, `Submodule.finrank_quotient_add_finrank,
    `LinearMap.finrank_range_add_finrank_ker,
    `Submodule.finrank_sup_add_finrank_inf_eq, `Submodule.rank_sup_add_rank_inf_eq,
    `rank_prod', `Module.finrank_prod, `Module.Basis.prod,
    `LinearEquiv.finrank_eq, `LinearEquiv.ofFinrankEq,
    `LinearMap.ker_eq_bot, `LinearMap.range_eq_top,
    `Submodule.eq_top_of_finrank_eq, `Submodule.finrank_eq_zero,
    `finrank_bot, `finrank_top, `finrank_span_eq_card,
    `linearIndependent_of_top_le_span_of_card_eq_finrank,
    `Module.Basis.constr, `Module.Basis.constr_basis, `Module.Basis.constr_range,
    `Module.Basis.injective_constr_of_linearIndependent, `LinearMap.exists_extend,
    `Matrix, `Matrix.mul_apply, `Matrix.mul_assoc, `Matrix.mulVec,
    `Matrix.mulVec_mulVec, `Matrix.one_mul, `Matrix.mul_one, `Matrix.one_apply,
    `LinearMap.toMatrix', `LinearMap.toMatrix'_mulVec,
    `LinearMap.toMatrix'_toLin', `Matrix.toLin', `Matrix.toLin'_toMatrix',
    `Matrix.toLin'_mul, `LinearMap.toMatrix'_comp, `LinearMap.comp,
    `LinearMap.comp_assoc, `Real.sin, `Real.cos, `Real.sin_add, `Real.cos_add,
    `midpoint, `midpoint_eq_smul_add, `smul_add, `add_smul, `smul_smul,
    `zero_smul, `one_smul, `div_mul_cancel₀, `Fintype.linearCombination,
    `Fintype.linearCombination_apply, `LinearIndependent.fintypeLinearCombination_injective,
    `Fin.sum_univ_two]
  for name in library do
    unless (env.find? name).isSome do throwError "Missing selected library declaration: {name}"
  let names := (localNames ++ library.toList).eraseDups.toArray.qsort
    (fun a b => a.toString < b.toString)
  let mut nodes : Array Json := #[]
  for name in names do
    let info := env.find? name |>.get!
    let project := `ILab.LinearAlgebra |>.isPrefixOf name
    match info with
    | .axiomInfo _ => if project then throwError "Project axiom: {name}"
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
    let typeDeps := info.type.getUsedConstants.toList.eraseDups.toArray.qsort
      (fun a b => a.toString < b.toString)
    let valueDeps := ((info.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
    let valueDeps := valueDeps.toList.eraseDups.toArray.qsort (fun a b => a.toString < b.toString)
    let signature ← Elab.Command.liftTermElabM <| Meta.ppExpr info.type
    let mod := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => "unknown"
    nodes := nodes.push <| Json.mkObj [
      ("id", toJson name.toString), ("kind", toJson kind), ("project", toJson project),
      ("module", toJson mod), ("signature", toJson signature.pretty),
      ("typeDependencies", toJson (typeDeps.map Name.toString)),
      ("valueDependencies", toJson (valueDeps.map Name.toString)),
      ("axioms", toJson ((axioms.map Name.toString).qsort (· < ·)))]
  IO.FS.createDirAll "verification"
  IO.FS.writeFile "verification/compiled.json" (Json.pretty (toJson nodes))
  logInfo m!"PASS: extracted and axiom-audited {localNames.length} project declarations and {library.size} selected library declarations from compiled Lean types and values."
