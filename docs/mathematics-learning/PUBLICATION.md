# Mathematics Learning publication — non-exercise release

Published through the existing authenticated DokuWiki and Hetzner WebFTP workflow on 18 October 2026. The eight approved lessons are preserved. The public interface now follows the actual deployed RQ-001 five-layer implementation, including Plain and Story. Full formalization of all synthetic/higher claims in the primary is not asserted.

## Public pages and announcement

The modified learning pages are under `mathematics_learning:higher_category_theory:synthetic_category_theory:`:

- `foundations`, `size`, `categories`, `functors`, `natural_transformations`, `yoneda`, `adjunctions`, `equivalences`: source-ordered anchors and 47 inline explanation controls.
- `coverage`: all 58 source items, individual status links and the complete assigned-exercise exclusions.
- `verification`: current build, compiler counts, precise scope and public QA evidence.
- `start`: the preserved eight-chapter reading path and current scoped status.

The homepage `start` contains the exact four-linked **New: Mathematics Learning** announcement immediately after **New: Explanation Layers**. Its existing Foundations Map learning link remains. [Browser readback of all four links](expanded-live-home-announcement.json) records the two internal destinations and both official lecturer links. The source/attribution page and the other existing learning landing pages remain available.

[Learning project](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:start) · [Coverage](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:coverage) · [Verification](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:verification) · [Graph](https://iontlab.org/formalization/mathematics-learning/) · [Homepage](https://iontlab.org/doku.php?id=start)

## Exercise correction

All 13 primary pages were audited, including embedded instructions: **17 assignment markers in 15 numbered items**. Solutions are withheld for **1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded opposite-invertibility step of 2.6, and 3.3**. Proposition 1.26's “Proof. Exercise.” is treated as an assignment. The main non-assigned hom-set criterion of 2.6 remains checked.

The previous public edition required correction: four lesson walkthroughs, six exercise-related authored Lean exports and two generated helpers were withdrawn from the current edition. The prepared expansion excludes 56 identified authored exports. Statements, numbering, lecturer attribution and unrelated foundations are preserved. Historical Git and wiki revisions can still contain withdrawn material; no history erasure is claimed. The emergency correction is merged as [PR #6](https://github.com/iontlab/geometry-of-intelligence/pull/6).

[Exclusion manifest](exercise-exclusions.json) · [Executable scope guard](../../tools/check-learning-exercise-scope.py) · [Current wiki snapshots](wiki-current/)

## Interaction and source binding

The actual live RQ-001 graph, renderer, registry, binding and release files were inspected and compared with the repository. Deployed enhancements absent from the older tracked version were preserved and reused. The existing plugin extension was explicitly approved by the user. [Isolation evidence](expanded-plugin-isolation.json) confirms that removing the two learning dispatch hooks/methods recovers the original RQ-001 PHP source byte-for-byte.

All 44 numbered source statements have inline access, with three additional scoped controls. The **Mathematics / Plain / Story / Lean / Verification** tabs resolve to individual source records. All 58 items are also accessible through the graph's source selector. There are 37 principal graph explanations; supporting nodes navigate to their main result, and technical helpers do not receive unrelated stories.

Exact source tuples include PDF page/item, chapter ID/revision/raw hash, rendered heading/anchor, role-specific server fragment hash, declaration/signature, module hash and pinned source commit. Current-source checks reject stale or inconsistent releases. An editor-only diagnostic publishes only source/fragment digests for binding capture; it exposes no source text or credentials. AI authorship is explicit; user publication authorization does not imply independent human review.

[All 47 live statement checks](expanded-live-all-statement-bindings.json) passed for the displayed statement, proof status and five tabs. [Plain and Story tests in all eight chapters](expanded-live-inline-qa.json) passed. Live checks also covered a non-exercise theorem's Story deep link, Proposition 1.26's withholding message, graph mode counts, module filtering, and a zero-result search for withdrawn proof exports. [Graph QA](expanded-live-graph-qa.json).

## Formalization and audit

The existing Lean 4.34.0 / Mathlib v4.34.0 project passed a clean build (8937 jobs), followed by compiler auditing of **225 declarations, including 116 authored declarations, in nine learning modules**. Only the existing foundational dependencies `propext`, `Classical.choice`, `Quot.sound` are allowed. Admitted expressions and project-added axioms are rejected.

The inventory tracks **132 obligations across 58 source items**: 112 checked in their precise Lean formulations, 15 assigned-solution withholding records, and five higher-foundation/model obligations. The 112 include definitions and assumed structures as well as proofs; they are not 112 new theorems. Type-universe category-size formulations are explicitly distinguished from literal ZF-set coding. Set-universe existence is assumed, not proved.

New work includes the ZFSet universe predicates and Russell consequence, source-specific category examples and laws, non-smallness formulations, a quasi-inverse equivalence criterion, the finite non-isomorphism distinction, and the cyclic-two/sign-group example. Exact Mathlib reuse includes category/functor/naturality fields, category isomorphism tests, pointed/free-vector/discrete/indiscrete adjunctions, non-exercise Yoneda consequences, equivalence operations, and endpoint-fixed path homotopies. [All authored signatures, source items and dependencies](../../formalization/mathematics-learning/verification/declaration-mapping.json) and [compiler-recorded Mathlib/external references](../../formalization/mathematics-learning/verification/mathlib-reuse.json) give the complete declaration-level record; no reused theorem is presented as an original iLab result.

The graph has **428 direct compiled project-local edges**. Blueprint: **109 mapped declarations / 70 visible edges**. Authored view: **116 declarations / 80 visible edges**. Full view: **225 declarations / 428 edges**. There are no invented conceptual or shortcut edges.

Exact checked Lean source commit: `ace59a04225eb98a769edb1943378d33a91aa204`. Branch: `codex/mathematics-learning-parity`. [Nine public module readbacks](expanded-public-source-readback.json) match the audited hashes. Release assets and final Git identifiers are recorded in `expanded-release-provenance.json`.

[Clean build](../../formalization/mathematics-learning/verification/expanded-clean-build.log) · [Audit summary](../../formalization/mathematics-learning/verification/audit-summary.json) · [Source hash lock](../../formalization/mathematics-learning/verification/expanded-audit.json) · [Reproduction instructions](../../formalization/mathematics-learning/verification/VERIFICATION.md)

## Protected RQ-001 and remaining limits

The RQ-001 compiler audit reproduced all **202 declarations byte-for-byte**, and all protected repository paths are unchanged. All **14 protected live graph/explanation assets** match baseline. The existing RQ-001 five-tab inspector and Story were tested in the browser after plugin deployment. [Compiler regression](../../formalization/mathematics-learning/verification/expanded-rq001-regression.json) · [Live UI check](expanded-live-rq001-ui.json) · [Asset readbacks](expanded-live-assets-readback.json).

Five source obligations require a specified higher model or different foundations: all-dimensional weak coherence (introduction p. 1); the full fundamental infinity-groupoid (pp. 1–2); types as infinity-groupoids (pp. 2–3); non-proof-irrelevant iterated identities (p. 2); and the Structure Identity Principle (p. 3). The checked path groupoid is an ordinary truncation. These boundaries, the type-universe formulation limits and universe-existence assumptions remain explicit; comprehensive verification of the full 13-page source is not claimed.

An official public URL and full-text republication authorization for the exact primary PDF remain unverified. The published text is independent source-ordered exposition with attribution; no private PDF or full extract was uploaded. Supplementary books remain supplementary. Independent human mathematical review is not claimed.
