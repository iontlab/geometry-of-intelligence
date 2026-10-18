# Source-faithful Mathematics Learning verification

The [source audit](../../../docs/mathematics-learning/original/native/source-audit.json) is authoritative for complete original-item coverage: **23 fully formalized, 15 exercise-affected, six eligible items pending**, out of 44 numbered items. Fourteen unnumbered editorial passage groups are not additional original theorems. The overall goal remains incomplete.

Checked Lean source commit: `0eb2f85a0ef04f1eda1d91c0c19faeccdb5e4f88`. The clean build passed with 8943 jobs; compiler extraction records **449 declarations, 188 authored declarations, 1686 direct local dependencies, 15 modules**. Source set-universe assumptions are explicit; ordinary Mathlib support is not counted as a different source theorem. No `sorry`, project-added axiom or dependency beyond `propext`, `Classical.choice`, `Quot.sound` is accepted.

[Audit summary](audit-summary.json), [clean build](expanded-clean-build.log), [source hash lock](expanded-audit.json), [module hashes](source-hashes.json), [declaration mapping](declaration-mapping.json), [external references](mathlib-reuse.json) and [axiom lists](all-declaration-axioms.txt).

```sh
lake clean rq001
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF=0eb2f85a0ef04f1eda1d91c0c19faeccdb5e4f88 node tools/build-learning-graph.mjs
python tools/audit-source-fidelity.py
python tools/check-learning-exercise-scope.py
node tools/check-learning-release.mjs
```

The reproducible native publication tools prepare exact manuscript-only reading flows, capture public source bytes and editor-attested digests, bind explanations, and verify deployed hashes. Actual writes use the established authenticated DokuWiki/WebFTP workflow. [Current publication evidence](../../../docs/mathematics-learning/native-publication-evidence/) records 235 panel checks, source readbacks and facsimile removal. RQ-001 source, evidence, shared plugin and dependency pins are unchanged.

Original assigned-exercise solutions remain withheld. All original author-written proofs and partial proofs remain published. Higher/synthetic foundations announced for later lectures are not invented. Independent human mathematical review is not claimed. Earlier records and Git revisions describe historical releases.
