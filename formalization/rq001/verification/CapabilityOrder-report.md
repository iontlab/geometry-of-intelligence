> Historical verification report. Local machine paths have been replaced with provenance labels. Commands, log references, and publication status below describe the earlier verification workspace, not the current public project. For reproducible public build instructions and the fresh combined audit, see [the package README](../README.md) and [PUBLIC-VERIFICATION.md](PUBLIC-VERIFICATION.md).

# RQ-001 Formalization II — verification report

PASS. CapabilityOrder.lean compiled in namespace ILab.RQ001. Both independent modules build together. No definitions or theorem statements changed. No intelligence predicate was introduced; capabilityMonotone_implies_extensional remains conditional on hmono. Nothing was published to iLab.

Environment:
- Lean 4.34.0, x86_64-w64-windows-gnu, Release.
- Lean commit: 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
- Mathlib v4.34.0, Git revision 5ed2965256430c3649e86755f9576b54eca72435.
- Project: [historical verification workspace].
- Final source: ILab/RQ001/CapabilityOrder.lean.
- Build: lake --old build (exit 0). Reuses unchanged dependencies without disabling proof checking. FourStateQuotient was replayed from its successful build; CapabilityOrder was freshly compiled.
- Audit: lake env lean CapabilityAudit.lean (exit 0). Imports both modules, prints axiom dependencies for all 19 named declarations in the new module, and scans 163 namespace declarations across both modules for axioms and admitted expressions.

Every source change (two proof bodies only):
1. capEq_iff_mutual: added `change Cap Succeeds S = Cap Succeeds T at h` to expose the definitional equality in h.
2. Its forward inclusion: `rw [CapEq, h] at hc ⊢` became `rw [h] at hc`.
3. Its reverse inclusion: `rw [CapEq, h] at hc ⊢` became `rw [h]`.
   Reason: CapEq was absent from the membership expressions being rewritten; each direction must rewrite the appropriate hypothesis or goal.
4. quotCap_injective, forward inclusion: `rw [h] at hc ⊢` became `rw [h] at hc`.
5. Its reverse inclusion: `rw [h] at hc ⊢` became `rw [h]`.
   Reason: one of the two rewrite locations already contained the right-hand side of h, causing the original tactic to fail.
No other edits. Complete diff: logs/capability/source.diff. The supplied original in Downloads is untouched.

Compiled definitions, abbreviation, and instance:
Cap; CapLE; CapEq; capSetoid; CapQuot; quotCap; QuotCapLE; capQuotPartialOrder; CapabilityMonotone; CapabilityExtensional.

Verified named theorems and exact dependencies:
| Theorem | Axiom dependencies |
| --- | --- |
| capLE_refl | None |
| capLE_trans | None |
| capEq_iff_mutual | propext, Quot.sound |
| quotCapLE_refl | None |
| quotCapLE_trans | None |
| quotCapLE_antisymm | propext, Quot.sound |
| quotCap_injective | propext, Quot.sound |
| quotCap_range | propext, Quot.sound |
| capabilityMonotone_implies_extensional | propext, Quot.sound |

capQuotPartialOrder also depends on propext and Quot.sound. All other named definitions/abbreviations have no axiom dependencies.

Zero sorry, admit, sorryAx, project-added axioms, native_decide auxiliary axioms, or hidden admitted propositions were found. propext and Quot.sound are Lean foundational axioms. Classical.choice is not used by this module's declarations.

Scope: capLE_refl and capLE_trans establish the preorder laws; the supplied source does not install a Preorder instance on R, and none was added. capSetoid / CapQuot quotient by capability equality. capQuotPartialOrder establishes the quotient partial order. quotCap_injective and quotCap_range identify the quotient with exactly the realized profiles; QuotCapLE is inclusion by definition. The attribution theorem is conditional only.

FourStateQuotient.lean SHA-256 before and after:
CB7132277F70879040917C06EE0CD1D9508438C1C543D5130156195F17FC8482
It was not modified. Neither formalization imports the other; only the audit imports both.
CapabilityOrder.lean final SHA-256:
D3C5E69AD2C7BDB14C3FDDD1B39388AA8D24502DFE91D600E73EF8CC41DDE1D9

Complete final Lake build output:
```text
⚠ [8924/8926] Replayed ILab.RQ001.FourStateQuotient
warning: ILab/RQ001/FourStateQuotient.lean:64:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [8925/8926] Built ILab.RQ001.CapabilityOrder (11s)
Build completed successfully (8926 jobs).
```

Complete axiom audit output:
```text
'ILab.RQ001.Cap' does not depend on any axioms
'ILab.RQ001.CapLE' does not depend on any axioms
'ILab.RQ001.capLE_refl' does not depend on any axioms
'ILab.RQ001.capLE_trans' does not depend on any axioms
'ILab.RQ001.CapEq' does not depend on any axioms
'ILab.RQ001.capEq_iff_mutual' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.capSetoid' does not depend on any axioms
'ILab.RQ001.CapQuot' does not depend on any axioms
'ILab.RQ001.quotCap' does not depend on any axioms
'ILab.RQ001.QuotCapLE' does not depend on any axioms
'ILab.RQ001.quotCapLE_refl' does not depend on any axioms
'ILab.RQ001.quotCapLE_trans' does not depend on any axioms
'ILab.RQ001.quotCapLE_antisymm' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.capQuotPartialOrder' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.quotCap_injective' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.quotCap_range' depends on axioms: [propext, Quot.sound]
'ILab.RQ001.CapabilityMonotone' does not depend on any axioms
'ILab.RQ001.CapabilityExtensional' does not depend on any axioms
'ILab.RQ001.capabilityMonotone_implies_extensional' depends on axioms: [propext, Quot.sound]
PASS: scanned 163 ILab.RQ001 declarations across both modules; no project axioms or admitted expressions.
```
