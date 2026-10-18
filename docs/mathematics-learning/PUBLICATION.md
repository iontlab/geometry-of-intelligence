# Native original manuscript publication — 18 October 2026

The complete Moser–Walde manuscript is now native DokuWiki text, MathJax mathematics and TikZJax vector diagrams in the existing eight chapters. The original is the sole main reading content. The former independent iLab exposition has been removed from the reading flow; Story / Fairy Tale, Plain Language, Mathematics, Lean and Verification remain interactive supplementary panels beside the original passages.

The original wording, notation, numbering, diagrams, proofs, partial proofs, 17 exercise markers, “Proof. Next time.”, references, affiliations and author AI-use disclosure are retained. Mathematics panels reproduce exact original passages. Statement labels use the established heading style. The eight chapter URLs, navigation and visual design are preserved.

**The overall formalization goal remains incomplete:** 23 of 44 numbered items are faithfully formalized, 15 are exercise-affected, and six eligible source items require further work. Compilation totals do not establish source fidelity. Independent human review is not claimed.

| Chapter | Native original | Numbered items | Fully formalized | Exercise-affected | Eligible pending |

|---|---|---:|---:|---:|---:|

| [Orientation / Foundations](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:foundations) | Complete, verified | 0 | 0 | 0 | 0 |

| [Size and Universes](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:size) | Complete, verified | 4 | 4 | 0 | 0 |

| [Categories and Isomorphisms](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:categories) | Complete, verified | 7 | 5 | 0 | 2 |

| [Functors and Representable Functors](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:functors) | Complete, verified | 8 | 2 | 4 | 2 |

| [Natural Transformations and Functor Categories](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:natural_transformations) | Complete, verified | 9 | 4 | 5 | 0 |

| [Yoneda Lemma](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:yoneda) | Complete, verified | 7 | 1 | 5 | 1 |

| [Adjunctions](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:adjunctions) | Complete, verified | 3 | 1 | 1 | 1 |

| [Equivalences of Categories](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:equivalences) | Complete, verified | 6 | 6 | 0 | 0 |

## Exact source-to-Lean coverage

The [source audit](original/native/source-audit.json) records every exact numbered item, original location and text hash, faithful declarations, correspondence and remaining prerequisites. [All authored signatures and source mappings](../../formalization/mathematics-learning/verification/declaration-mapping.json) are compiler-derived. Fourteen editorial passage groups cover the unnumbered introduction and remarks; they are not additional numbered theorems.

Outstanding eligible original items:

- **1.8** — Set is complete. Pointed sets, topological spaces and vector spaces still need explicit bounded set codes, operation-preserving Mathlib correspondences, and non-smallness proofs for those exact collections.

- **1.10** — Set is complete. The isomorphism characterizations for pointed sets, vector spaces and topological spaces require the pending exact structured-set encodings from 1.8.

- **1.13** — The forgetful, added-basepoint, free-vector-space, discrete and indiscrete functors need set-coded object/hom implementations and operation-preserving correspondences. Existing type-universe examples alone do not close this item.

- **1.16** — Needs set codes for all small categories and their functors, hom-set membership in the small universe, non-smallness of the exact object collection, and the huge-category inclusion. Construction 1.15 category-law exercise must remain withheld.

- **2.7** — The ordinary Mathlib Yoneda result is retained as independent support. Still needs a representation theorem for the actual small-set-valued representables and their natural isomorphisms, preserving the source universe domains without publishing the assigned 1.19/2.1/2.4 solutions.

- **3.2** — The four actual example adjunctions require the pending structured-set categories and functors from 1.8/1.13, including the exact free-vector-space carrier and source universe bounds.

The introduction’s all-dimensional coherence, full fundamental infinity-groupoid, higher identity types and Structure Identity Principle await the intended later foundations. No missing axioms are invented. The existing ordinary path/groupoid and equality results remain explicitly limited supporting work.

Assigned solutions remain withheld for **1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded step of 2.6, and 3.3**. The original supplied portions remain verbatim. Mixed item 2.6 is not counted as fully formalized. [Exercise exclusions](exercise-exclusions.json).

## Build and provenance

Checked Lean source commit: [`0eb2f85a0ef04f1eda1d91c0c19faeccdb5e4f88`](https://github.com/iontlab/geometry-of-intelligence/commit/0eb2f85a0ef04f1eda1d91c0c19faeccdb5e4f88). Branch: `codex/source-faithful-native-manuscript`. Lean 4.34.0 and Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435` are unchanged.

The clean build completed with **8943 jobs**. The compiler audit covers **449 declarations in 15 modules**, including **188 authored declarations** and **1686 direct project dependencies**. The allowed foundational dependencies remain `propext`, `Classical.choice`, `Quot.sound`; no admitted expressions or project-added axioms are accepted. The source hierarchy’s existence remains an explicit assumption.

[Clean build log](../../formalization/mathematics-learning/verification/expanded-clean-build.log) · [Compiler audit and source hash lock](../../formalization/mathematics-learning/verification/expanded-audit.json) · [Current audit summary](../../formalization/mathematics-learning/verification/audit-summary.json) · [Reproduction](../../formalization/mathematics-learning/verification/VERIFICATION.md).

## Live publication checks

- Eight public chapter sources exactly match the reviewed native drafts and authenticated editor digests. The original text projection is unchanged by heading formatting.

- **47 controls × five layers = 235 successful panel checks**. All **60 distinct declaration verification deep links** exposed by the chapter panels select the corresponding audited graph entry. The theorem graph’s five layers also pass.

- All 18 learning assets match the upload hashes. Current chapter captures show zero MathJax errors and zero facsimile images.

- All 17 obsolete PNG URLs return HTTP 404. The current repository copies are removed. The original PDF remains unchanged at SHA-256 `5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc`.

- All 14 protected RQ-001 live assets and protected repository paths remain unchanged. Existing compiler-regression evidence retains its 202-declaration baseline.

[Current evidence](native-publication-evidence/) includes source readbacks, native rendering, all panel checks, asset hashes, media removal and RQ-001 regression. [Historical facsimile evidence](original-publication-evidence/) is retained as an explicitly superseded record; it does not describe the current presentation.

## Rights and authorship

Publication of the complete primary manuscript was explicitly authorized by the site owner. Copyright remains with the original rights holders; the repository code license and wiki-wide license do not relicense it. No author endorsement is asserted. Story and Plain Language are independently authored iLab educational explanations with AI assistance. Supplementary books remain private references.
