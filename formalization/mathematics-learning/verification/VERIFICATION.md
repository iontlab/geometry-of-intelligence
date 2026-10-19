# Source-faithful Mathematics Learning verification

The [source audit](../../../docs/mathematics-learning/original/native/source-audit.json) is authoritative for complete original-item coverage. **29 of 44 numbered items are faithfully formalized; 15 are exercise-affected; 0 eligible numbered items remain pending.** Prospective higher foundations are explicitly deferred. Compilation totals do not establish source fidelity. Independent human review is not claimed. Fourteen unnumbered editorial passage groups are not additional original theorems.

Checked Lean source commit: `ebde0f04b46bc3cfa906d06b749e4954549f545c`. The clean build passed with 8962 jobs; compiler extraction records **816 declarations, 427 authored declarations, 4030 direct local dependencies, 34 modules**. Source set-universe assumptions are explicit; ordinary Mathlib support is not counted as a different source theorem. No `sorry`, project-added axiom or dependency beyond `propext`, `Classical.choice`, `Quot.sound` is accepted.

[Audit summary](audit-summary.json), [clean build](expanded-clean-build.log), [source hash lock](expanded-audit.json), [module hashes](source-hashes.json), [declaration mapping](declaration-mapping.json), [external references](mathlib-reuse.json) and [axiom lists](all-declaration-axioms.txt).

```sh
lake clean rq001
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF=ebde0f04b46bc3cfa906d06b749e4954549f545c node tools/build-learning-graph.mjs
python tools/audit-source-fidelity.py
python tools/check-learning-exercise-scope.py
node tools/check-learning-release.mjs
```

The reproducible native publication tools prepare exact manuscript-only reading flows, capture public source bytes and editor-attested digests, bind explanations, and verify deployed hashes. Actual writes use the established authenticated DokuWiki/WebFTP workflow. [Current publication evidence](../../../docs/mathematics-learning/native-publication-evidence/) records 235 panel checks, source readbacks and facsimile removal. RQ-001 source, evidence, shared plugin and dependency pins are unchanged.

Original assigned-exercise solutions remain withheld. All original author-written proofs and partial proofs remain published. Higher/synthetic foundations announced for later lectures are not invented. Independent human mathematical review is not claimed. Earlier records and Git revisions describe historical releases.

Theorem 2.1 now has four checked partial declarations: evaluation alpha maps to alpha_c(id_c), the candidate component function f maps to F(f)(u), and their two defining equations. The candidate is represented only by component functions. Its naturality, mutual inverseness with evaluation, and naturality in c and F remain assigned exercises. The complete Yoneda theorem is not verified. The 29 fully formalized / 15 exercise-affected item counts are unchanged.

G1–G10 add 31 typed raw-data declarations and definitional readbacks, reuse existing mappings for 1.19 and 2.2, and correct the Section 3 introduction link. Category/functor laws, naturality, inverse checks and triangle identities remain assigned. Corollary 2.6 receives only the opposite-composition formula, not its assigned isomorphism premise. The complete Yoneda lemma and representable adjunction theorem remain unverified as source theorems.
