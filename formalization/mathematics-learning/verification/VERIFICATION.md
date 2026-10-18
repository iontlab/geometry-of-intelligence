# Non-exercise Mathematics Learning verification

Source commit: `ace59a04225eb98a769edb1943378d33a91aa204`. Nine learning modules passed a clean Lake build (8937 jobs) and the compiler audit: **225 compiled declarations, 116 authored declarations, 428 direct local edges**. The graph has 109 Blueprint mappings (70 visible edges), 37 principal five-layer explanations, and 58 source-item inspector entries. All 47 inline statement controls were tested on the live wiki; Plain and Story were tested in all eight chapters.

[Audit summary](audit-summary.json), [clean build](expanded-clean-build.log), [source hash lock](expanded-audit.json), [current module hashes](source-hashes.json), [declaration mapping](declaration-mapping.json), [exact external references / Mathlib reuse](mathlib-reuse.json), and [axiom lists](all-declaration-axioms.txt) describe the current release. The older `clean-build.log` is historical and is not the evidence for this expansion.

The compiler rejects project axioms, admitted expressions, and transitive axiom dependencies outside `propext`, `Classical.choice`, `Quot.sound`. Definitions and assumed structures are not existence proofs. Mathlib reuse is not claimed as original iLab mathematics.

The [58-item inventory](../../../docs/mathematics-learning/obligations.json) tracks 132 obligations: 112 checked in their precise Lean formulations, 15 withholding records covering 17 assigned exercise markers, and five higher-foundation/model obligations. Category-size statements use explicitly scoped type universes rather than a literal encoding of all source categories as ZF sets. Universe existence is assumed, not proved. Full synthetic/higher category theory, non-proof-irrelevant identity structure and the Structure Identity Principle are not claimed.

Solutions assigned in 1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded step in 2.6, and 3.3 are withheld. The main non-assigned criterion of 2.6 remains. [Exercise exclusions](../../../docs/mathematics-learning/exercise-exclusions.json) identify the precise boundary. Current pages and graph were corrected; old Git/wiki revisions may still retain withdrawn material.

```sh
lake clean rq001
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF=ace59a04225eb98a769edb1943378d33a91aa204 node tools/build-learning-graph.mjs
python tools/check-learning-exercise-scope.py
node tools/check-learning-release.mjs
```

The source hash lock is recorded only after a successful clean build and compiler audit. Explanation generation additionally requires captured current wiki revisions, raw bytes, exact anonymous rendered fragments, and editor-attested fragment digests. `build-learning-release.py` consumes this evidence without writing to a server. Deployment remains the authenticated DokuWiki/WebFTP workflow.

[Fresh RQ-001 regression](expanded-rq001-regression.json) reproduces all 202 compiled declarations byte-for-byte. Its four source modules, original graph, audit evidence and dependency configuration are unchanged. All 14 protected live graph/explanation assets also match their baseline. Independent human mathematical review is not claimed.
