# Source-faithful Mathematics Learning verification

The [source audit](../../../docs/mathematics-learning/original/native/source-audit.json) is authoritative for complete original-item coverage. **29 of 44 numbered items are faithfully formalized; 15 are exercise-affected; 0 eligible numbered items remain pending.** Prospective higher foundations are explicitly deferred. Compilation totals do not establish source fidelity. Independent human review is not claimed. Fourteen unnumbered editorial passage groups are not additional original theorems.

Checked Lean source commit: `0070c175806aa22b8227c86af53c5ca78bdb8d34`. The clean build passed with 8960 jobs; compiler extraction records **781 declarations, 392 authored declarations, 3836 direct local dependencies, 32 modules**. Source set-universe assumptions are explicit; ordinary Mathlib support is not counted as a different source theorem. No `sorry`, project-added axiom or dependency beyond `propext`, `Classical.choice`, `Quot.sound` is accepted.

[Audit summary](audit-summary.json), [clean build](expanded-clean-build.log), [source hash lock](expanded-audit.json), [module hashes](source-hashes.json), [declaration mapping](declaration-mapping.json), [external references](mathlib-reuse.json) and [axiom lists](all-declaration-axioms.txt).

```sh
lake clean rq001
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF=0070c175806aa22b8227c86af53c5ca78bdb8d34 node tools/build-learning-graph.mjs
python tools/audit-source-fidelity.py
python tools/check-learning-exercise-scope.py
node tools/check-learning-release.mjs
```

The reproducible native publication tools prepare exact manuscript-only reading flows, capture public source bytes and editor-attested digests, bind explanations, and verify deployed hashes. Actual writes use the established authenticated DokuWiki/WebFTP workflow. [Current publication evidence](../../../docs/mathematics-learning/native-publication-evidence/) records 235 panel checks, source readbacks and facsimile removal. RQ-001 source, evidence, shared plugin and dependency pins are unchanged.

Original assigned-exercise solutions remain withheld. All original author-written proofs and partial proofs remain published. Higher/synthetic foundations announced for later lectures are not invented. Independent human mathematical review is not claimed. Earlier records and Git revisions describe historical releases.
