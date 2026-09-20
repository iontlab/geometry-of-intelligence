> Historical verification report. Local machine paths have been replaced with provenance labels. Commands, log references, and publication status below describe the earlier verification workspace, not the current public project. For reproducible public build instructions and the fresh combined audit, see [the package README](../README.md) and [PUBLIC-VERIFICATION.md](PUBLIC-VERIFICATION.md).

# RQ-001 Formalization IV — second verification pass

PASS. The v2 common-codomain formulation compiles after the compilation-only fixes below. All four modules build together. No mathematical meaning was changed. All theorem signatures were compared verbatim with v2 and match exactly. The final universal property compiled exactly as intended, with pointwise surjectivity and retained-probe factorization assumptions intact:

```lean
∃! h : Z ⟶ transformationQuotientFunctor X Probe Obs eval,
  a ≫ h = transformationQuotientNatTrans X Probe Obs eval
```

No ULift construction, new hypothesis, or independent target universe was introduced. Functoriality, naturality, local probe factorization, the factorization triangle, and uniqueness all remain proved. Nothing was published to iLab.

## Exact environment and commands

Lean 4.34.0, x86_64-w64-windows-gnu, Release.
Lean commit: 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
Mathlib v4.34.0, Git revision 5ed2965256430c3649e86755f9576b54eca72435.
Project: [historical verification workspace].
Build: lake --old build (exit 0). The modified module was freshly compiled; unchanged modules/dependencies were reused. This flag does not disable proof checking.
Audit: lake env lean TransformationAudit.lean (exit 0). All four modules were imported together.

Source: ILab/RQ001/TransformationSufficientQuotient.lean.
Compiled artifact: .lake/build/lib/lean/ILab/RQ001/TransformationSufficientQuotient.olean.
Final source SHA-256: E04891B0FB52C7A9E6C7A67A35006A3D4C428B0E80119001CDAF649BD93858C3.

## Every source change relative to supplied v2

1. transformationQuotientFunctor.map: wrapped Quotient.lift in TypeCat.ofHom and supplied `(s := transformSetoid X Probe Obs eval e)`. This constructs a bundled Type-category morphism and explicitly identifies the quotient relation. The underlying map is unchanged.
2. transformationQuotientFunctor.map_id and map_comp: replaced `funext q` with `ext q` to handle bundled morphism equality. Removed the final `exact transformEq_refl ...` in each proof because `rw [hx]` already closes its goal; leaving the extra tactic caused “No goals to be solved”.
3. transformationQuotientNatTrans.app: wrapped the same quotient function in TypeCat.ofHom. Its naturality proof uses `ext x` instead of `funext x` for bundled morphisms.
4. quotientFactorNatTrans.app: wrapped the same chosen-preimage quotient function in TypeCat.ofHom. Its naturality proof uses `ext z` instead of `funext z`. Added `symm` after applying nat_kernel_le_transformEq to match the direction of the existing calc chain to the naturality goal; the equality and naturality statement are unchanged.
5. quotientFactor_triangle: replaced `apply CategoryTheory.NatTrans.ext; funext e; funext x` with `ext e x`, which handles both natural-transformation and bundled-component extensionality.
6. quotientFactor_unique: replaced the analogous three extensionality steps with `ext e z`. Replaced both `congrFun (CategoryTheory.congr_app ...) x` calls with `ConcreteCategory.congr_hom (CategoryTheory.congr_app ...) x` to evaluate equal bundled morphisms at an element.

No other edits. Full exact diff is included below and in logs/transformation-v2/source.diff. The supplied v2 file in Downloads was not modified. Remaining style warnings were not changed.

## Verified declarations and axiom audit

All 20 named declarations are preserved under namespace ILab.RQ001. The full per-declaration output below provides both the complete inventory and exact dependency list. Only Lean foundational axioms propext, Classical.choice, and Quot.sound occur. They are not project-added assumptions.

The audit additionally scanned the types and values of 202 ILab.RQ001 declarations across all four modules and rejected any axiom declaration or admitted expression. A source-token scan passed.

Confirmed zero: sorry, admit, sorryAx, project-added axioms, native_decide auxiliary axioms, and hidden admitted propositions.

## Integrity of prior modules

All three prior sources have unchanged contents and SHA-256 hashes:
- FourStateQuotient: CB7132277F70879040917C06EE0CD1D9508438C1C543D5130156195F17FC8482
- CapabilityOrder: D3C5E69AD2C7BDB14C3FDDD1B39388AA8D24502DFE91D600E73EF8CC41DDE1D9
- SymmetryObstruction: B17E16126A44018F1D44A24A40BD58B7607829D8537857DA77CAE167766A2351

All four formalization modules import only Mathlib, not each other. The separate audit imports all four.

## Complete final build output
```text
⚠ [8925/8928] Replayed ILab.RQ001.FourStateQuotient
warning: ILab/RQ001/FourStateQuotient.lean:64:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8926/8928] Replayed ILab.RQ001.SymmetryObstruction
warning: ILab/RQ001/SymmetryObstruction.lean:97:4: Try `simp at hne` instead of `simpa using hne`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8927/8928] Built ILab.RQ001.TransformationSufficientQuotient (11s)
warning: ILab/RQ001/TransformationSufficientQuotient.lean:131:6: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ILab/RQ001/TransformationSufficientQuotient.lean:140:6: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ILab/RQ001/TransformationSufficientQuotient.lean:194:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ILab/RQ001/TransformationSufficientQuotient.lean:197:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: ILab/RQ001/TransformationSufficientQuotient.lean:255:14: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (8928 jobs).
```

## Complete per-declaration axiom audit

```text
'ILab.RQ001.TransformEq' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformEq_refl' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformEq_symm' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformEq_trans' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformSetoid' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.TransformQuot' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformEq_map' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformationQuotientFunctor' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.transformationQuotientNatTrans' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.probeDesc' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.probe_factors_through_quotient' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.PointwiseSurjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.ProbesFactorThrough' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.nat_kernel_le_transformEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.chosenPreimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.chosenPreimage_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.quotientFactorNatTrans' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.quotientFactor_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.quotientFactor_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.transformation_sufficient_quotient_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: scanned 202 ILab.RQ001 declarations across all four modules; no project axioms or admitted expressions.
```

## Complete source diff

```diff
diff --git "a/[original-inputs]/TransformationSufficientQuotient_v2.lean" "b/ILab\\RQ001\\TransformationSufficientQuotient.lean"
index 4dff4de..a81735b 100644
--- "a/[original-inputs]/TransformationSufficientQuotient_v2.lean"
+++ "b/ILab\\RQ001\\TransformationSufficientQuotient.lean"
@@ -115,7 +115,7 @@ theorem transformEq_map {e d : E} (φ : e ⟶ d)
 def transformationQuotientFunctor : E ⥤ Type uX where
   obj e := TransformQuot X Probe Obs eval e
   map {e d} φ :=
-    Quotient.lift
+    TypeCat.ofHom <| Quotient.lift (s := transformSetoid X Probe Obs eval e)
       (fun x : X.obj e =>
         (Quotient.mk _ (X.map φ x) : TransformQuot X Probe Obs eval d))
       (by
@@ -123,16 +123,15 @@ def transformationQuotientFunctor : E ⥤ Type uX where
         apply Quotient.sound
         exact transformEq_map X Probe Obs eval φ h)
   map_id e := by
-    funext q
+    ext q
     refine Quotient.inductionOn q ?_
     intro x
     apply Quotient.sound
     have hx : X.map (𝟙 e) x = x := by
       simpa using congrFun (X.map_id e) x
     rw [hx]
-    exact transformEq_refl X Probe Obs eval e x
   map_comp {e d k} φ ψ := by
-    funext q
+    ext q
     refine Quotient.inductionOn q ?_
     intro x
     apply Quotient.sound
@@ -140,14 +139,13 @@ def transformationQuotientFunctor : E ⥤ Type uX where
         X.map (φ ≫ ψ) x = X.map ψ (X.map φ x) := by
       simpa using congrFun (X.map_comp φ ψ) x
     rw [hx]
-    exact transformEq_refl X Probe Obs eval k (X.map ψ (X.map φ x))
 
 /-- The canonical quotient maps assemble into a natural transformation. -/
 def transformationQuotientNatTrans :
     X ⟶ transformationQuotientFunctor X Probe Obs eval where
-  app e := fun x => Quotient.mk _ x
+  app e := TypeCat.ofHom (fun x => Quotient.mk _ x)
   naturality e d φ := by
-    funext x
+    ext x
     rfl
 
 /-- A retained local probe descends to the local quotient. -/
@@ -243,12 +241,13 @@ def quotientFactorNatTrans
     (hsurj : PointwiseSurjective X a)
     (hfactors : ProbesFactorThrough X Probe Obs eval a) :
     Z ⟶ transformationQuotientFunctor X Probe Obs eval where
-  app e := fun z =>
-    Quotient.mk _ (chosenPreimage X a hsurj e z)
+  app e := TypeCat.ofHom (fun z =>
+    Quotient.mk _ (chosenPreimage X a hsurj e z))
   naturality e d φ := by
-    funext z
+    ext z
     apply Quotient.sound
     apply nat_kernel_le_transformEq X Probe Obs eval a hfactors
+    symm
     calc
       a.app d (X.map φ (chosenPreimage X a hsurj e z))
           = Z.map φ
@@ -271,9 +270,7 @@ theorem quotientFactor_triangle
     (hfactors : ProbesFactorThrough X Probe Obs eval a) :
     a ≫ quotientFactorNatTrans X Probe Obs eval a hsurj hfactors
       = transformationQuotientNatTrans X Probe Obs eval := by
-  apply CategoryTheory.NatTrans.ext
-  funext e
-  funext x
+  ext e x
   apply Quotient.sound
   apply nat_kernel_le_transformEq X Probe Obs eval a hfactors
   exact chosenPreimage_spec X a hsurj e (a.app e x)
@@ -288,15 +285,13 @@ theorem quotientFactor_unique
     (htriangle :
       a ≫ h = transformationQuotientNatTrans X Probe Obs eval) :
     h = quotientFactorNatTrans X Probe Obs eval a hsurj hfactors := by
-  apply CategoryTheory.NatTrans.ext
-  funext e
-  funext z
+  ext e z
   rcases hsurj e z with ⟨x, rfl⟩
   have hh :
       h.app e (a.app e x)
         = (transformationQuotientNatTrans X Probe Obs eval).app e x := by
     simpa using
-      congrFun (CategoryTheory.congr_app htriangle e) x
+      ConcreteCategory.congr_hom (CategoryTheory.congr_app htriangle e) x
   have hq :
       (quotientFactorNatTrans X Probe Obs eval a hsurj hfactors).app e
           (a.app e x)
@@ -304,7 +299,7 @@ theorem quotientFactor_unique
     have htri :=
       quotientFactor_triangle X Probe Obs eval a hsurj hfactors
     simpa using
-      congrFun (CategoryTheory.congr_app htri e) x
+      ConcreteCategory.congr_hom (CategoryTheory.congr_app htri e) x
   exact hh.trans hq.symm
 
 /-- **Transformation-sufficient quotient theorem.**
```
