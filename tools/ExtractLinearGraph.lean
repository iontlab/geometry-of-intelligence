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
    `IsGLB, `Nat.dvd_gcd, `Nat.gcd_dvd_left, `DirectSum.toModule, `DirectSum.linearMap_ext, `DirectSum.toModule_lof, `LinearMap.pi, `LinearEquiv.ofLinearMap, `Polynomial.algHom_ext, `AlgEquiv.ofAlgHom,
    `LinearMap.ker_noncommProd_eq_of_supIndep_ker, `Finset.map_noncommProd, `Matrix.charpoly_mul_comm, `Real.hasDerivAt_exp, `HasDerivAt.mul,
    `Submodule.exists_isCompl, `LinearMap.ker_eq_bot, `LinearMap.ker_eq_top, `Submodule.span_induction, `Finset.sum_range_succ,
    `Module.End.genEigenspace_nat, `Module.End.maxGenEigenspace_eq_genEigenspace_finrank, `Module.End.mapsTo_genEigenspace_of_comm, `Module.End.disjoint_genEigenspace, `Module.End.independent_maxGenEigenspace, `Module.End.iSup_maxGenEigenspace_eq_top, `Module.End.isNilpotent_restrict_sub_algebraMap, `Module.End.exists_ker_pow_eq_ker_pow_succ, `Module.End.ker_pow_constant, `Module.End.ker_pow_eq_ker_pow_finrank_of_le, `Submodule.isCompl_iff_disjoint, `LinearMap.charpoly_prodMap, `Module.End.exists_isNilpotent_isSemisimple, `Module.End.isNilpotent_isSemisimple_unique, `Algebra.commute_of_mem_adjoin_singleton_of_commute,
    `Matrix.aeval_self_charpoly, `Matrix.minpoly_dvd_charpoly, `Matrix.isIntegral, `Matrix.minpoly_toLin', `LinearMap.minpoly_toMatrix, `minpoly.monic, `minpoly.aeval, `minpoly.dvd_iff, `minpoly.unique, `minpoly.degree_le_of_ne_zero, `minpoly.aeval_modByMonic_minpoly, `minpoly.algEquiv_eq, `minpoly.eq_of_linearIndependent, `minpoly.natDegree_pos, `minpoly.subsingleton, `minpoly.eq_X_sub_C, `minpoly.zero, `minpoly.one, `Module.End.aeval_apply_of_hasEigenvector, `Module.End.hasEigenvalue_iff_isRoot, `Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd, `Polynomial.aeval_algHom_apply, `LinearEquiv.conjAlgEquiv,
    `Matrix.charpoly_of_isUpperTriangular, `Matrix.charpoly_fromBlocks_zero₂₁, `Module.Basis.flag, `Module.Basis.mem_flag_iff_repr_eq_zero, `Module.Basis.flag_mono, `Module.Basis.flag_zero, `Module.Basis.flag_last, `Polynomial.Splits.of_dvd, `Polynomial.Splits.of_degree_le_one, `Submodule.prodEquivOfIsCompl, `Submodule.comapSubtypeEquivOfLe, `Polynomial.roots_multiset_prod_X_sub_C,
    `LinearMap.finrank_eigenspace_le, `LinearMap.finrank_maxGenEigenspace_eq, `Module.End.eigenspaces_iSupIndep, `DirectSum.IsInternal.collectedBasis, `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top, `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute, `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo, `Matrix.maxGenEigenspace_toLin_diagonal_eq_eigenspace, `Module.End.trace_eq_sum_roots_charpoly_of_splits, `Matrix.charpoly_diagonal, `Matrix.charpoly_map, `Polynomial.Splits.natDegree_eq_card_roots,
    `Polynomial.aeval, `Polynomial.algHom_ext, `Polynomial.aeval_X, `Polynomial.aeval_mul, `Polynomial.aeval_add, `Polynomial.coeff_mul, `Polynomial.div_modByMonic_unique, `Polynomial.modByMonic_add_div, `Polynomial.degree_modByMonic_lt, `Polynomial.degree_mul, `Polynomial.dvd_iff_isRoot, `Polynomial.card_roots, `Polynomial.card_roots', `Polynomial.funext, `Polynomial.le_rootMultiplicity_iff, `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd, `Polynomial.rootMultiplicity_pos, `Polynomial.Splits.eq_prod_roots, `Complex.exists_root, `Complex.isAlgClosed, `IsAlgClosed.splits,
    `Module.End.eigenspace_def, `Module.End.mem_eigenspace_iff, `Module.End.hasEigenvector_iff, `Module.End.eigenvectors_linearIndependent', `Module.End.hasEigenvalue_iff_isRoot_charpoly, `LinearMap.eval_charpoly, `LinearMap.charpoly_toMatrix, `Matrix.charpoly_monic, `Matrix.charpoly_natDegree_eq_dim, `Matrix.charpoly_units_conj, `Matrix.eval_charpoly, `Matrix.trace_eq_neg_charpoly_coeff, `Real.coe_fib_eq, `Nat.fib_add_two,
    `hammingDist, `hammingDist_eq_zero, `hammingDist_comm, `hammingDist_triangle, `hammingDist_comp, `Module.card_eq_pow_finrank, `Submodule.mkQ, `Submodule.ker_mkQ, `Submodule.mkQ_surjective,
    `Module.Basis.orientation_eq_iff_det_pos, `Module.Basis.orientation_eq_or_eq_neg, `Module.Basis.orientation_neg_single, `Module.Basis.adjustToOrientation, `Module.Basis.orientation_adjustToOrientation, `Module.Ray.ne_neg_self, `Quotient.lift, `Quotient.sound, `Matrix.rank_submatrix_le, `Matrix.trace, `Matrix.trace_add, `Matrix.trace_smul, `Matrix.trace_mul_comm, `Matrix.trace_units_conj, `Matrix.trace_transpose, `LinearMap.trace, `LinearMap.trace_eq_matrix_trace, `Matrix.submatrix, `Setoid, `Nat.card_congr,
    `Matrix.permMatrixHom, `Matrix.det_permutation, `Equiv.swap_inv, `Equiv.Perm.swapFactors, `Equiv.Perm.sign_mul, `Equiv.Perm.sign_inv, `Equiv.Perm.sign_swap, `Equiv.Perm.sign_prod_list_swap, `alternatingGroup, `alternatingGroup_eq_sign_ker, `card_alternatingGroup, `nat_card_alternatingGroup, `Equiv.Perm.sign_eq_prod_prod_Ioi, `Matrix.det_apply', `Matrix.det_fromBlocks_zero₂₁, `Equiv.Perm.sign_sumCongr, `Fintype.card_perm, `Matrix.permMatrix_mul, `Equiv.Perm.permMatrix,
    `Matrix.det_mul, `Matrix.det_transvection_of_ne, `Matrix.det_diagonal,
    `Matrix.det_nonsing_inv, `Matrix.GeneralLinearGroup.det,
    `Matrix.adjugate_fin_succ_eq_det_submatrix, `Matrix.mul_adjugate, `Matrix.adjugate_mul,
    `Matrix.inv_def, `Matrix.adjugate_fin_two_of, `Matrix.det_smul_inv_mulVec_eq_cramer,
    `LinearMap.det_toMatrix_eq_det_toMatrix, `LinearMap.det_toMatrix,
    `LinearMap.det_comp, `LinearMap.isUnit_iff_isUnit_det, `LinearEquiv.det,
    `Real.sin_sq_add_cos_sq,
    `Matrix.det_succ_column, `Matrix.det_succ_row, `Matrix.det_updateCol_add, `Matrix.det_updateCol_smul,
    `Matrix.det_transpose, `Matrix.rank_of_det_ne_zero, `Matrix.exists_mulVec_eq_zero_iff,
    `Matrix.isUnit_iff_isUnit_det, `Matrix.rank_transpose, `Matrix.det_permute',
    `dotProduct_comm, `crossProduct, `cross_apply, `cross_anticomm, `cross_self,
    `dot_self_cross, `dot_cross_self, `triple_product_permutation,
    `triple_product_eq_det, `EuclideanSpace.norm_eq, `EuclideanSpace.inner_eq_star_dotProduct,
    `InnerProductGeometry.norm_toLp_symm_crossProduct, `Matrix.det_updateRow_add, `Matrix.det_updateRow_smul,
    `Matrix.det_zero_of_row_eq, `Matrix.det_eq_zero_of_row_eq_zero, `Matrix.det_updateRow_add_smul_self,
    `Matrix.det_of_isUpperTriangular, `Matrix.det_fin_two, `Matrix.det_fin_three,
    `AlternatingMap.eq_smul_basis_det, `Matrix.det_smul, `Matrix.det_permute,
    `zorn_subset, `zorn_le, `IsChain, `IsMax, `PartialOrder, `upperBounds,
    `linearIndepOn_sUnion_of_directed, `IsChain.directedOn,
    `Polynomial.basisMonomials, `Polynomial.coe_basisMonomials,
    `Module.Basis.extendLe, `Module.Basis.range_extendLe,

    `Matrix.rank, `Matrix.rank_transpose, `Matrix.rank_eq_finrank_span_cols,
    `Matrix.rank_eq_finrank_span_row, `Matrix.rank_eq_finrank_range_toLin,
    `Matrix.rank_mul_eq_left_of_isUnit_det, `Matrix.rank_mul_eq_right_of_isUnit_det,
    `Matrix.exists_rank_normal_form, `Matrix.transpose_nonsing_inv,
    `Module.Basis.ofEquivFun, `Module.Basis.ofEquivFun_repr_apply,
    `Matrix.toLinearEquiv, `Submodule.exists_finset_span_eq_linearIndepOn,
    `finrank_span_finset_eq_card,

    `Module.Basis.equivFun, `Module.Basis.equivFun_symm_apply,
    `LinearMap.toMatrix_comp, `LinearMap.toMatrix_mulVec_repr,
    `LinearMap.toMatrix_id_eq_basis_toMatrix, `Module.Basis.toMatrix,
    `Module.Basis.toMatrix_apply, `Module.Basis.toMatrix_mul_toMatrix_flip,
    `Matrix.inv_eq_left_inv,

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
    `Filter.Tendsto.const_smul, `tendsto_const_nhds, `Submodule.mem_span_set', `Submodule.span_empty, `Submodule.subset_span, `Submodule.span_le, `Submodule.span_iUnion, `Submodule.span_eq, `Finsupp.linearCombination, `Finsupp.range_linearCombination, `Fintype.linearCombination, `Fintype.range_linearCombination, `linearIndependent_iff, `linearIndependent_iff_finset_linearIndependent, `linearIndependent_empty_type, `linearIndependent_unique_iff, `LinearIndependent.injective, `linearIndependent_iff_injective_fintypeLinearCombination, `Fintype.linearCombination_apply, `Fintype.linearCombination_apply_single, `Module.Basis.mk, `Module.Basis.coe_mk, `Module.Basis.ofSpan, `Module.Basis.ofSpan_subset, `Module.Basis.extend, `Module.Basis.extendLe, `Module.Basis.subset_extendLe, `Module.Basis.extendLe_subset, `Module.Basis.repr_self, `Module.Basis.linearIndependent, `Module.Basis.span_eq, `LinearIndependent.update, `LinearIndependent.fintype_card_le_finrank, `Module.finrank_eq_card_basis, `Submodule.finrank_le, `Submodule.eq_top_of_finrank_eq, `Module.rank_lt_aleph0_iff, `Polynomial.not_finite, `Complex.finrank_real_complex, `Matrix.stdBasis, `Matrix.stdBasis_eq_single, `Matrix.matrix_eq_sum_single, `Module.finrank_matrix, `Matrix.transpose_mul, `Matrix.transpose_transpose, `Matrix.mul_smul, `Matrix.smul_mul, `Matrix.mul_add, `Matrix.add_mul, `LinearMap.toMatrix, `LinearMap.toMatrix_apply, `LinearMap.toMatrix_id, `Module.finrank_linearMap, `Matrix.GeneralLinearGroup, `Matrix.single, `Module.Basis.map, `Matrix.IsRowEchelon, `Matrix.IsLeadingEntry, `Matrix.IsPivotedBy, `Matrix.IsPivotedBy.rank_eq, `Matrix.rowScale, `Matrix.rowScale_mul, `Matrix.rowScale_mul_rowScale, `Matrix.swap, `Matrix.swap_mul_self, `Matrix.transvection, `Matrix.transvection_mul_transvection_same, `Matrix.transvection_mul_apply_same, `Matrix.diagonal_transvection_induction_of_det_ne_zero, `Matrix.GeneralLinearGroup.rowScale, `Matrix.GeneralLinearGroup.swap, `Matrix.GeneralLinearGroup.transvection, `Matrix.rank, `Matrix.row_ne_zero_iff_exists_isLeadingEntry, `Matrix.isUnit_iff_isUnit_det, `mul_eq_one_comm, `Matrix.mulVec_mulVec]
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
