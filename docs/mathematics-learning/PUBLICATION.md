# Native original manuscript publication — 18 October 2026

The complete Moser–Walde manuscript is now native DokuWiki text, MathJax mathematics and TikZJax vector diagrams in the existing eight chapters. The original is the sole main reading content. The former independent iLab exposition has been removed from the reading flow; Story / Fairy Tale, Plain Language, Mathematics, Lean and Verification remain interactive supplementary panels beside the original passages.

The original wording, notation, numbering, diagrams, proofs, partial proofs, 17 exercise markers, “Proof. Next time.”, references, affiliations and author AI-use disclosure are retained. Mathematics panels reproduce exact original passages. Statement labels use the established heading style. The eight chapter URLs, navigation and visual design are preserved.

**29 of 44 numbered items are faithfully formalized; 15 are exercise-affected; 0 eligible numbered items remain pending.** Prospective higher foundations are explicitly deferred. Compilation totals do not establish source fidelity. Independent human review is not claimed.

| Chapter | Native original | Numbered items | Fully formalized | Exercise-affected | Eligible pending |
|---|---|---:|---:|---:|---:|
| [Orientation / Foundations](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:foundations) | Complete, verified | 0 | 0 | 0 | 0 |
| [Size and Universes](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:size) | Complete, verified | 4 | 4 | 0 | 0 |
| [Categories and Isomorphisms](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:categories) | Complete, verified | 7 | 7 | 0 | 0 |
| [Functors and Representable Functors](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:functors) | Complete, verified | 8 | 4 | 4 | 0 |
| [Natural Transformations and Functor Categories](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:natural_transformations) | Complete, verified | 9 | 4 | 5 | 0 |
| [Yoneda Lemma](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:yoneda) | Complete, verified | 7 | 2 | 5 | 0 |
| [Adjunctions](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:adjunctions) | Complete, verified | 3 | 2 | 1 | 0 |
| [Equivalences of Categories](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:equivalences) | Complete, verified | 6 | 6 | 0 | 0 |

## Exact source-to-Lean coverage

The [source audit](original/native/source-audit.json) records every exact numbered item, original location and text hash, faithful declarations, correspondence and remaining prerequisites. [All authored signatures and source mappings](../../formalization/mathematics-learning/verification/declaration-mapping.json) are compiler-derived. Fourteen editorial passage groups cover the unnumbered introduction and remarks; they are not additional numbered theorems.

No eligible numbered item remains pending.

The introduction’s all-dimensional coherence, full fundamental infinity-groupoid, higher identity types and Structure Identity Principle await the intended later foundations. No missing axioms are invented. The existing ordinary path/groupoid and equality results remain explicitly limited supporting work.

Assigned solutions remain withheld for **1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded step of 2.6, and 3.3**. The original supplied portions remain verbatim. Mixed item 2.6 is not counted as fully formalized. [Exercise exclusions](exercise-exclusions.json).

## Build and provenance

Checked Lean source commit: [`0070c175806aa22b8227c86af53c5ca78bdb8d34`](https://github.com/iontlab/geometry-of-intelligence/commit/0070c175806aa22b8227c86af53c5ca78bdb8d34). Branch: `codex/source-faithful-native-manuscript`. Lean 4.34.0 and Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435` are unchanged.

The clean build completed with **8960 jobs**. The compiler audit covers **781 declarations, 392 authored declarations, 3836 direct local dependencies, 32 modules**. The allowed foundational dependencies remain `propext`, `Classical.choice`, `Quot.sound`; no admitted expressions or project-added axioms are accepted. The source hierarchy’s existence remains an explicit assumption.

[Publication PR #9](https://github.com/iontlab/geometry-of-intelligence/pull/9). The source commit above pins every checked declaration; subsequent release commits record deployment evidence.

[Clean build log](../../formalization/mathematics-learning/verification/expanded-clean-build.log) · [Compiler audit and source hash lock](../../formalization/mathematics-learning/verification/expanded-audit.json) · [Current audit summary](../../formalization/mathematics-learning/verification/audit-summary.json) · [Reproduction](../../formalization/mathematics-learning/verification/VERIFICATION.md).

## Live publication checks

- Eight public chapter sources exactly match the reviewed native drafts and authenticated editor digests. The original text projection is unchanged by heading formatting.

- **47 controls × five layers = 235 successful panel checks**. All **99 distinct declaration verification deep links** exposed by the chapter panels select the corresponding audited graph entry. All 38 graph explanation records passed five layers each: **190 additional checks**.

- All 18 learning assets match the upload hashes. Current chapter captures show zero MathJax errors and zero facsimile images.

- All 17 obsolete PNG URLs return HTTP 404. The current repository copies are removed. The original PDF remains unchanged at SHA-256 `5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc`.

- All 14 protected RQ-001 live assets and protected repository paths remain unchanged. Existing compiler-regression evidence retains its 202-declaration baseline.

[Current evidence](native-publication-evidence/) includes source readbacks, native rendering, all panel checks, asset hashes, media removal and RQ-001 regression. [Historical facsimile evidence](original-publication-evidence/) is retained as an explicitly superseded record; it does not describe the current presentation.

## Rights and authorship

Publication of the complete primary manuscript was explicitly authorized by the site owner. Copyright remains with the original rights holders; the repository code license and wiki-wide license do not relicense it. No author endorsement is asserted. Story and Plain Language are independently authored iLab educational explanations with AI assistance. Supplementary books remain private references.

## Partial Yoneda construction release r12

The original 13-page Moser–Walde manuscript, page 9, supplies the forward map alpha -> alpha_c(id_c) and candidate inverse components (alpha_u)_x(f) = F(f)(u). Lean checks these two functions in the existing set-universe representation and their two defining equations. The candidate is deliberately not packaged as a natural transformation.

The first assigned check (well-defined natural transformation / naturality) and the second assigned check (mutual inverseness and naturality in c and F) remain open. No complete Yoneda equivalence or theorem is exported. The existing representable functor is a reused prerequisite, not a newly solved exercise.

Release r12 passed the clean compiler audit (8961 jobs), source-fidelity and exercise-boundary checks, graph/release integrity and 28 navigation tests. Live tests passed: 235 wiki layer checks, 195 graph layer checks, 116 source narrative checks, all four new declaration scope checks, 45 asset hashes and eight unchanged chapter bindings. All 781 earlier declarations, the existing 96 narratives (including corrected inverse story), original manuscript, shared plugin, dependency pins and RQ-001 remain unchanged.

See publication.json for exact commits and counts, release-checks.log for offline checks, live-integrity.json for deployed hashes, and the panel/graph JSON and screenshot for browser evidence. The previous release evidence remains historical and unchanged.

[Current release evidence](yoneda-construction-evidence/README.md).
