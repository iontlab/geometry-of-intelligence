> Historical verification report. Local machine paths have been replaced with provenance labels. Commands, log references, and publication status below describe the earlier verification workspace, not the current public project. For reproducible public build instructions and the fresh combined audit, see [the package README](../README.md) and [PUBLIC-VERIFICATION.md](PUBLIC-VERIFICATION.md).

# RQ-001 Formalization III — Symmetry Obstruction verification

PASS. The supplied SymmetryObstruction.lean compiled without any source changes. All definitions, theorem statements, proofs, names, comments, and imports are preserved byte-for-byte. No theorem was weakened or strengthened. Nothing was published to iLab.

## Environment

Lean 4.34.0, x86_64-w64-windows-gnu, Release.
Lean commit: 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b.
Mathlib v4.34.0.
Mathlib Git revision: 5ed2965256430c3649e86755f9576b54eca72435.
Project: [historical verification workspace].
Source: ILab/RQ001/SymmetryObstruction.lean.
Compiled artifact: .lake/build/lib/lean/ILab/RQ001/SymmetryObstruction.olean.

## Commands and scope

Actual build: lake --old build (exit 0). The new module was freshly compiled; unchanged modules and dependencies were reused. The --old flag avoids rebuilding unchanged modules merely because transitive dependency traces changed; it does not disable Lean proof checking.
Audit: lake env lean SymmetryAudit.lean (exit 0).

The project library target includes all three modules. The separate audit imports all three simultaneously. None of the three formalization modules imports another; each imports Mathlib.

No finiteness, decidability, or nonemptiness assumption on V was added. The supplied Group and MulAction setting remains unchanged, including the empty-space case. The result is the standard transitive-action obstruction to nontrivial invariant subsets. No intelligence predicate or intelligence-related necessity/sufficiency theorem was introduced.

The actual declaration namespace is ILab.RQ001. SymmetryObstruction is the module filename and a section name, not an extra namespace; the supplied naming was preserved.

## Complete source change list

None. The copied source is byte-for-byte identical to the supplied file. The new style warning at line 97 was left untouched because it is not a compilation error.

Original and compiled source SHA-256:
B17E16126A44018F1D44A24A40BD58B7607829D8537857DA77CAE167766A2351

## All compiled declarations and exact axiom dependencies

All names below are prefixed ILab.RQ001.

| Declaration | Kind | Axiom dependencies |
| --- | --- | --- |
| ActionInvariant | Definition | None |
| ActionTransitive | Definition | None |
| actionInvariant_empty | Theorem | propext |
| actionInvariant_univ | Theorem | propext |
| invariant_membership_iff | Theorem | None |
| transitive_invariant_eq_empty_or_univ | Theorem | propext, Classical.choice, Quot.sound |
| transitive_invariant_nonempty_eq_univ | Theorem | propext, Classical.choice, Quot.sound |
| no_nonempty_proper_invariant | Theorem | propext, Classical.choice, Quot.sound |

These are Lean foundational axioms, not project-added assumptions. Classical.choice is used in the last three theorem dependencies; no additional classical hypothesis was added to any theorem statement.

The audit printed dependencies for every named declaration in this file and scanned the types and values of all 171 ILab.RQ001 declarations across the three modules. The scan rejects axiom declarations and admitted expressions. Source token scanning also passed.

Confirmed zero: sorry, admit, sorryAx, project-added axioms, native_decide auxiliary axioms, and hidden admitted propositions.

## Consistency with Formalizations I and II

All three modules build successfully in the same project and import successfully together. The two prior files were not modified; their SHA-256 hashes remain:

FourStateQuotient.lean:
CB7132277F70879040917C06EE0CD1D9508438C1C543D5130156195F17FC8482

CapabilityOrder.lean:
D3C5E69AD2C7BDB14C3FDDD1B39388AA8D24502DFE91D600E73EF8CC41DDE1D9

## Complete final build output
```text
⚠ [8925/8927] Replayed ILab.RQ001.FourStateQuotient
warning: ILab/RQ001/FourStateQuotient.lean:64:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
⚠ [8926/8927] Built ILab.RQ001.SymmetryObstruction (11s)
warning: ILab/RQ001/SymmetryObstruction.lean:97:4: Try `simp at hne` instead of `simpa using hne`

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (8927 jobs).
```

## Complete axiom audit output

```text
'ILab.RQ001.ActionInvariant' does not depend on any axioms
'ILab.RQ001.ActionTransitive' does not depend on any axioms
'ILab.RQ001.actionInvariant_empty' depends on axioms: [propext]
'ILab.RQ001.actionInvariant_univ' depends on axioms: [propext]
'ILab.RQ001.invariant_membership_iff' does not depend on any axioms
'ILab.RQ001.transitive_invariant_eq_empty_or_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.transitive_invariant_nonempty_eq_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'ILab.RQ001.no_nonempty_proper_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS: scanned 171 ILab.RQ001 declarations across all three modules; no project axioms or admitted expressions.
```
