> Historical verification report. Local machine paths have been replaced with provenance labels. Commands, log references, and publication status below describe the earlier verification workspace, not the current public project. For reproducible public build instructions and the fresh combined audit, see [the package README](../README.md) and [PUBLIC-VERIFICATION.md](PUBLIC-VERIFICATION.md).

# RQ-001 compilation and verification

Result: PASS. All 15 named theorems compile, with unchanged statements and definitions. Nothing was published to iLab. The supplied file remains unchanged in Downloads; the compiled copy is ILab/RQ001/FourStateQuotient.lean, in its original namespace ILab.RQ001.

## Exact environment

Lean (version 4.34.0, x86_64-w64-windows-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)
Lake version 5.0.0-src+293d5d0 (Lean version 4.34.0)
Mathlib tag: v4.34.0
Mathlib Git revision: 5ed2965256430c3649e86755f9576b54eca72435
Mathlib source: https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435
Transitive dependencies are pinned in lake-manifest.json. Mathlib is a local path dependency at ./mathlib, checked out at the exact revision above.

## Every source change

Line 210, proof of card_state: replaced `native_decide` with `decide`.

The original file compiled without syntax, elaboration, namespace, or theorem errors. Its native_decide proof generated the auxiliary axiom ILab.RQ001.card_state._native.native_decide.ax_1_1 in Lean 4.34.0. The single proof-term change removes that axiom to satisfy the no-added-axioms requirement. Ordinary decide proves exactly the same statement by kernel reduction. No definitions, theorem statements, imports, comments, or other proof steps changed. The existing unnecessarySimpa warning was intentionally left unchanged because it is cosmetic.

## Verification

Successful final command: lake --old build
Exit code: 0
Complete output: logs/build-final.log (also reproduced below).
Compiled artifact: .lake/build/lib/lean/ILab/RQ001/FourStateQuotient.olean

Axiom audit command: lake env lean Audit.lean
Exit code: 0
Full output: logs/axioms-final.log.
All 15 named theorems were audited. The only remaining axiom dependencies are Lean's standard foundational axioms propext, Classical.choice, and Quot.sound. There is no sorryAx, native_decide auxiliary axiom, or project-added axiom. Source scan confirms zero occurrences of sorry, admit, axiom, or native_decide.

Final source SHA-256: CB7132277F70879040917C06EE0CD1D9508438C1C543D5130156195F17FC8482

Verified claims and corresponding theorems:
- Task equivalence is exactly q equality: taskEq_iff_q_eq.
- Enriched equivalence is equality of states: fullEq_iff_eq.
- Strict refinement: strict_refinement.
- Coarse task classes are represented by q: taskClass_eq_iff_taskEq (taskClass is definitionally State.q).
- Update does not descend: no_update_descends.
- Exactly four states: card_state, with enumeration in state_cases.

## Build environment notes and full log index

Lean/Elan were initially absent. Installed Elan 4.2.4 without modifying PATH, then the pinned Lean toolchain. All project work occurred outside the iLab workspace.

Mathlib's cache downloader reported successful decompression but most Mathlib artifacts were absent. Direct extraction of the downloaded archives with the toolchain's leantar succeeded. The initial builds were interrupted because they were rebuilding the library without those cache artifacts. After extraction, Lake completed the original and final target builds. The --old flag reused unchanged library modules instead of propagating dependency rebuilds; it does not disable Lean's checking of the target source. The target was actually compiled after the single source edit.

logs/setup.log: complete Lake update / toolchain / dependency / cache setup output.
logs/build-original.log: interrupted initial Lake build.
logs/build-original-cached.log: interrupted build before cache extraction was repaired.
logs/compile-original.log: direct Lean attempt before extraction repair; missing Mathlib.olean.
logs/cache-extract.log: direct extraction output (empty; exit 0).
logs/lookup.log: diagnostic cache lookup output.
logs/build-original-restored.log: successful build of unchanged original source after extraction repair.
logs/axioms-original.log: original proof axiom dependencies.
logs/build-final.log: successful final build, complete output below.
logs/axioms-final.log: successful final proof axiom audit.

## Complete final build output

```text
⚠ [8924/8925] Built ILab.RQ001.FourStateQuotient (11s)
warning: ILab/RQ001/FourStateQuotient.lean:64:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (8925 jobs).
```
