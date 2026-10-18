# Mathematics Learning verification — exercise exclusions

Assigned exercise solutions are excluded from the current learning publication. Statements, numbering and attribution are preserved. The 13-page audit identifies 17 markers in 15 items; see [the exclusion manifest](../../../docs/mathematics-learning/exercise-exclusions.json).

The retained two public modules rebuilt successfully. The compiler auditor checked all 65 retained declarations (14 authored) and their transitive foundational dependencies. The graph contains 232 direct local edges and 9 Blueprint mappings. No admitted expression, project-added assumption, or dependency outside `propext`, `Classical.choice`, `Quot.sound` is permitted.

Source commit: `2481cbf1b85e35c29f0f71c5aa4cf5edd353c724`. Lean 4.34.0 and the existing pinned Mathlib v4.34.0 are unchanged. [Source hashes](source-hashes.json), [declaration mapping](declaration-mapping.json), [axiom lists](all-declaration-axioms.txt), and [compiler result](declaration-audit.log) describe this release. The retained identity laws, inverse uniqueness and walking-isomorphism example are non-exercise material. The old clean-build log records the historical pre-exclusion release, not a new clean-build claim.

Reproduce using the existing project:

```sh
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF=2481cbf1b85e35c29f0f71c5aa4cf5edd353c724 node tools/build-learning-graph.mjs
```

The four RQ-001 modules and their existing evidence are unchanged. The broader non-exercise formalization and five-layer interaction update remain in preparation. This emergency correction does not claim comprehensive completion.

The previous four chapter walkthroughs and six exercise-related Lean exports were withdrawn. Historical Git commits and wiki revisions may still contain them; the current edition does not erase history. Private prepared exercise solutions will not be included in future releases.
