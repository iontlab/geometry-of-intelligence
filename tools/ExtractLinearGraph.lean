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
    `Fin.sum_univ_two, `Finset.sum_add_distrib, `Finset.mul_sum, `Equiv.swap,
    `Matrix.mulVec_zero, `mul_left_cancel₀,
    `And, `Or, `Not, `Iff, `Exists, `True, `False,
    `And.intro, `And.left, `And.right, `Iff.intro, `Iff.mp, `Iff.mpr,
    `Exists.intro, `False.elim, `Classical.em, `Classical.not_not,
    `Classical.not_forall, `Classical.byContradiction, `Classical.choice,
    `not_and_or, `not_or, `imp_iff_not_or, `and_comm, `or_comm,
    `and_assoc, `or_assoc, `and_or_left, `or_and_left, `not_exists,
    `forall_comm, `exists_comm, `forall_and, `exists_or,
    `Nat.lt_succ_self, `Nat.lt_irrefl,
    `Set, `Set.ext, `Set.Subset.antisymm, `Set.empty_subset,
    `Set.singleton_subset_iff, `Set.mem_powerset_iff, `Set.mem_iInter, `Set.mem_iUnion,
    `Finset.card_powerset, `Finset.sum_range_succ,
    `Nat.rec, `Nat.succ_ne_zero, `Nat.succ.inj, `Nat.factorial, `Nat.factorial_succ,
    `Nat.mul_succ, `Nat.strong_induction_on, `Nat.find, `Nat.find_spec, `Nat.find_min,
    `Nat.Prime, `Nat.primeFactorsList, `Nat.prod_primeFactorsList,
    `Nat.prime_of_mem_primeFactorsList, `Nat.not_prime_iff_exists_mul_eq,
    `List.mem_append, `List.prod_append, `List.prod_pos, `Nat.Prime.pos,
    `Setoid, `Quotient.mk_surjective, `Quotient.eq_iff_equiv,
    `Set.disjoint_left, `Set.image, `Set.preimage, `Function.comp,
    `Function.Injective, `Function.Surjective, `Function.Bijective,
    `Function.LeftInverse.injective, `Function.RightInverse.surjective,
    `Equiv.ofBijective, `Equiv.curry, `Equiv.bijective,
    `Equiv.symm_apply_apply, `Equiv.apply_symm_apply,
    `Fintype.card_congr, `Fintype.bijective_iff_injective_and_card,
    `Fintype.bijective_iff_surjective_and_card, `Subtype.val_injective, `Prod.mk.injEq,
    `Group, `CommGroup, `Subgroup, `mul_assoc, `one_mul, `mul_one,
    `inv_mul_cancel, `mul_inv_cancel, `mul_right_cancel, `zpow_add,
    `Subgroup.one_mem, `Subgroup.mul_mem, `Subgroup.inv_mem, `Subgroup.map,
    `Subgroup.zpowers, `Subgroup.mem_zpowers_iff,
    `ZMod, `ZMod.card, `Fintype.card_perm, `Equiv.Perm,
    `QuotientGroup.rightRel, `QuotientGroup.rightRel_apply,
    `QuotientGroup.quotientRightRelEquivQuotientLeftRel,
    `Subgroup.card_eq_card_quotient_mul_card_subgroup,
    `Subgroup.groupEquivQuotientProdSubgroup, `Subgroup.rightCosetEquivSubgroup,
    `Nat.card_congr, `Nat.card_prod, `dvd_mul_left,
    `MonoidHom, `AddMonoidHom, `MulEquiv, `MonoidHom.ker, `MonoidHom.range,
    `MonoidHom.ker_eq_bot_iff, `MonoidHom.range_eq_top,
    `MulEquiv.ofBijective, `MulEquiv.symm, `MulEquiv.trans, `MulEquiv.refl,
    `Equiv.permCongrHom, `Subgroup.closure, `Subgroup.subset_closure,
    `Int.eq_one_or_neg_one_of_mul_eq_one, `ZMod.intCast_surjective,
    `Real.exp, `Real.exp_add, `Real.exp_pos, `Real.log,
    `Real.log_exp, `Real.exp_log, `Real.log_mul, `Units.mk0,
    `add_mul, `mul_add, `add_assoc, `add_comm, `add_neg_cancel,
    `mul_inv_cancel₀, `inv_mul_cancel₀, `mul_eq_zero, `neg_mul,
    `Complex, `Complex.normSq, `Complex.normSq_apply, `Complex.I_mul_I,
    `Complex.ofReal_injective, `Complex.arg, `Complex.arg_le_pi,
    `Complex.neg_pi_lt_arg, `Complex.norm_mul_cos_add_sin_mul_I,
    `Complex.normSq_eq_norm_sq, `norm_mul, `norm_add_le,
    `Real.cos_add_two_pi, `Real.sin_add_two_pi,
    `Ring, `CommRing, `NonUnitalRing, `RingHom, `IsUnit, `IsField,
    `IsField.toField, `Field.toIsField, `CharP.char_is_prime_or_zero,
    `ringChar, `ringChar.eq, `Int.castRingHom,
    `Polynomial, `Polynomial.coeff, `Polynomial.coeff_add, `Polynomial.coeff_mul,
    `Polynomial.eval, `Polynomial.evalRingHom, `Polynomial.eval_add,
    `Polynomial.eval_mul, `Polynomial.eval_X, `Polynomial.eval_X_pow,
    `Polynomial.degree_zero, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ,
    `Submodule.mem_sup, `Submodule.mem_inf, `Submodule.mem_iInf,
    `Submodule.eq_bot_iff, `Submodule.mem_iSup_of_mem, `Submodule.sum_mem,
    `Submodule.disjoint_def, `LinearEquiv.ofBijective,
    `DirectSum, `DirectSum.linearEquivFunOnFintype,
    `Complex.real_smul, `Complex.smul_re, `Complex.smul_im,
    `inv_smul_smul₀, `Finset.smul_sum,
    `LinearMap.map_add, `LinearMap.map_smul, `LinearMap.map_sub,
    `Submodule.map, `Submodule.comap, `Submodule.mem_map, `Submodule.mem_comap,
    `LinearMap.codRestrict, `LinearEquiv.symm, `LinearEquiv.trans,
    `Polynomial.toFinsuppIsoLinear, `AddMonoidAlgebra.coeffLinearEquiv,
    `finsuppLEquivDirectSum, `DFinsupp.finite_support, `Finsupp,
    `Module.Basis.ext,
    `Submodule.quotientRel, `Submodule.quotientRel_def, `Submodule.Quotient.eq,
    `Submodule.Quotient.mk_eq_zero, `Submodule.Quotient.mk_add, `Submodule.Quotient.mk_smul,
    `Submodule.mkQ, `Submodule.ker_mkQ, `Submodule.mkQ_surjective,
    `Submodule.liftQ, `Submodule.liftQ_mkQ, `LinearMap.quotKerEquivRange_apply_mk,
    `LinearMap.quotKerEquivOfSurjective, `LinearMap.proj, `LinearMap.snd,
    `Filter.Tendsto, `tendsto_nhds_unique, `Filter.Tendsto.add,
    `Filter.Tendsto.const_smul, `tendsto_const_nhds]
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
