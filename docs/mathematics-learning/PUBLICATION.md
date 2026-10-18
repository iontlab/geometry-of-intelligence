> Publication correction, 18 October 2026: assigned exercise solutions are withdrawn. The current release retains 14 authored / 65 compiled declarations. Earlier counts below describe the historical initial release. See [exercise exclusions](exercise-exclusions.json) and the current verification record.

# Mathematics Learning — publication report

Published and live-checked on 18 October 2026. The sole subsection name is **Higher Category Theory**; **Synthetic Category Theory** is the first learning project inside it.

## Architecture and reuse

The existing DokuWiki installation (Mort 2026-07-14c, PHP 8.2.34, `dokuwiki` template) uses colon namespaces, `start` landing pages, underscore separators and wiki-native navigation rows. The configured `sidebar` page does not exist; no new sidebar was introduced. One Mathematics Learning link was appended to the existing homepage Foundations Map row. All other homepage content is unchanged.

The separate research Mathematics namespace is `math:`. The new namespace is `mathematics_learning:`. All educational prose remains canonical in DokuWiki. Existing MathJax notation and rendering are reused. The same Story → Plain Language → Mathematics → Lean → Verification sequence, source attribution, story keys and analogy limits are expressed in native wiki sections. The seven RQ-001 explanation records and their source-binding/release gates are unchanged; no duplicate explanation renderer was installed.

The existing `iontlab/geometry-of-intelligence` repository and Lake project are reused. New sources are isolated in `ILab.MathematicsLearning`. The compiler extractor is the original auditor with learning imports, namespace and output path; all rejection rules are retained. The metadata builder keeps source hashes, prohibited-token checks and dependency completeness checks, and validates curated graph IDs. The static graph reuses `app.js`, `blueprint-view.js`, `mathematics-view.js`, existing styles and their data schema with minimal namespace/label/link adaptations.

Production deployment used authenticated Hetzner konsoleH/WebFTP: a scoped ZIP in private account Home was extracted into `public_html/formalization/mathematics-learning/`. No existing RQ-001 asset, plugin, server configuration, routing or dependency version changed. An initial ZIP permission issue produced 403 responses and was corrected to 0644 files / 0755 for the new directory. All final static content hashes match the committed artifacts. This is an explicit deployment; no automatic GitHub–DokuWiki synchronization or new hosting infrastructure exists.

## Pages created and modified

Sixteen new pages were saved through the authenticated internal browser, visually/DOM checked and independently read back as raw public source. Every final source exactly matches its prepared text. The homepage is the only pre-existing page modified.

| Page ID | Public page | Change |
| --- | --- | --- |
| `mathematics_learning:algebra:start` | [Algebra](https://iontlab.org/doku.php?id=mathematics_learning:algebra:start) | Created |
| `mathematics_learning:higher_category_theory:start` | [Higher Category Theory](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:start) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:adjunctions` | [Adjunctions: a natural correspondence of maps](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:adjunctions) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:categories` | [Categories and isomorphisms](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:categories) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:coverage` | [Synthetic Category Theory — coverage and proof status](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:coverage) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:equivalences` | [Equivalences and the walking isomorphism](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:equivalences) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:foundations` | [Orientation: ordinary, higher and synthetic categories](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:foundations) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:functors` | [Functors and representable functors](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:functors) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:natural_transformations` | [Natural transformations and functor categories](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:natural_transformations) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:size` | [Size and universes](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:size) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:sources` | [Synthetic Category Theory — sources and conventions](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:sources) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:start` | [Synthetic Category Theory](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:start) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:verification` | [Selected ordinary-category formalization — verification](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:verification) | Created |
| `mathematics_learning:higher_category_theory:synthetic_category_theory:yoneda` | [Yoneda: an object through its maps](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:yoneda) | Created |
| `mathematics_learning:start` | [Mathematics Learning](https://iontlab.org/doku.php?id=mathematics_learning:start) | Created |
| `mathematics_learning:topology:start` | [Topology](https://iontlab.org/doku.php?id=mathematics_learning:topology:start) | Created |
| `start` | [iLab homepage](https://iontlab.org/doku.php?id=start) | One navigation link |

## Source verification and coverage

The supplied ZIP's three PDFs were extracted into private local storage outside the repository. Actual file access, title/authors/edition, page processing, visual title-page inspection and SHA-256 checks passed before source-dependent work. The verified counts are **13**, **583** and **299** pages. [Source identities and hashes](README.md) and the canonical [source page](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:sources) distinguish the binding Moser–Walde installment from Cisinski–Cnossen–Walde's September 18, 2026 draft and Riehl's supplied second edition.

All **58 identified mathematical items** are covered: **44 numbered items** and **14 substantive unnumbered items**. There are no known omitted source items. Constituent examples within a numbered item are included. The machine-readable [coverage manifest](coverage.json) retains original numbering, PDF pages, dependencies, source-proof status, educational-layer status, scoped Lean mappings and public URLs. The eight lessons cover orientation, size, categories, functors, natural transformations, Yoneda, adjunctions and equivalences.

All eight lessons have original Story / Fairy Tale, Plain Language and Mathematics sections, followed by Lean and Verification sections that distinguish checked results from feasibility or written mathematics. The first orientation lesson remains bounded: the future localisation, fibration, Kan-extension and limit/colimit syllabus is explicitly announced material, not expanded into the first lesson.

The source's exercises remain identified as exercises. Theorem 3.7's source proof is deferred; the added proof sketch is independently supplied and makes classical choice explicit. Proposition 3.9 is also proved directly with both target objects accounted for. Riehl's covariant Yoneda presentation, hom-bijection adjunction definition and choice convention are distinguished from the primary's notation. The supplementary synthetic draft's foundations and stronger surjectivity data are not silently substituted for ordinary definitions.

## Formalization

The clean root-package Lake build passed for all six modules. The toolchain remains Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`; Mathlib v4.34.0, revision `5ed2965256430c3649e86755f9576b54eca72435`.

All **73 compiled learning declarations**, including generated helpers, passed the full axiom audit; **20 are authored declarations**. No admitted expressions, project axioms, prohibited tokens or proof-checking bypasses were introduced. The only permitted foundational dependencies remain `propext`, `Classical.choice`, `Quot.sound`. The exact claims, assumptions, signatures and source locations are available in the [verification report](../../formalization/mathematics-learning/verification/VERIFICATION.md), [machine-readable mappings](../../formalization/mathematics-learning/verification/declaration-mapping.json), source hashes and complete build/audit logs.

Every row below compiled and passed the declaration audit. Definitions and instances are checked constructions, not additional theorem claims. Declaration names have prefix `ILab.MathematicsLearning.`.

| Declaration | Source | Primary item | Checked mathematical scope |
| --- | --- | --- | --- |
| `identity_padded_composite` | [BasicCategoryTheory.lean:22](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L22) | 1.5 | A composable pair is unchanged after inserting identities |
| `inverse_unique` | [BasicCategoryTheory.lean:27](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L27) | 1.11 | A right inverse and a left inverse of the same arrow agree |
| `mapped_inverse_left` | [BasicCategoryTheory.lean:36](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L36) | 1.14 | A functor preserves the first inverse equation |
| `mapped_inverse_right` | [BasicCategoryTheory.lean:42](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L42) | 1.14 | A functor preserves the second inverse equation |
| `mappedIso` | [BasicCategoryTheory.lean:48](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L48) | 1.14 | Package the two mapped arrows as an isomorphism |
| `mappedIso_eq_mapIso` | [BasicCategoryTheory.lean:55](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L55) | 1.14 | The construction equals Mathlib Functor.mapIso |
| `composite_naturality` | [BasicCategoryTheory.lean:61](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L61) | 1.20 / 1.23 | Vertical composition satisfies naturality |
| `vertical_composite_component` | [BasicCategoryTheory.lean:73](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/BasicCategoryTheory.lean#L73) | 1.23 | Functor-category composition has the stated components |
| `Room` | [WalkingIsomorphism.lean:16](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L16) | 3.8 | Inductive object type with north and south constructors |
| `roomFintype` | [WalkingIsomorphism.lean:21](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L21) | 3.8 | Complete finite enumeration of the two objects |
| `OneRoom` | [WalkingIsomorphism.lean:25](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L25) | 1.25 | Inductive object type with one constructor |
| `roomCategory` | [WalkingIsomorphism.lean:29](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L29) | 3.8 | Small category with singleton hom types on Room |
| `oneRoomCategory` | [WalkingIsomorphism.lean:34](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L34) | 1.25 | Small category with singleton hom types on OneRoom |
| `roomIso` | [WalkingIsomorphism.lean:40](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L40) | 3.8 | Explicit isomorphism between each ordered pair of rooms |
| `includeRoom` | [WalkingIsomorphism.lean:45](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L45) | 3.9 | Functor selecting north from the one-object category |
| `collapseRoom` | [WalkingIsomorphism.lean:50](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L50) | 3.9 | Functor collapsing both rooms to the sole object |
| `walkingEquivalence` | [WalkingIsomorphism.lean:55](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L55) | 3.4 / 3.9 | Explicit bundled adjoint equivalence, including a triangle law |
| `inclusion_not_surjective` | [WalkingIsomorphism.lean:65](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L65) | 3.6 / 3.9 | The inclusion is not literally surjective on objects |
| `inclusion_essentially_surjective` | [WalkingIsomorphism.lean:72](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L72) | 3.6 / 3.9 | Every room is isomorphic to the selected image object |
| `room_cardinality` | [WalkingIsomorphism.lean:76](https://github.com/iontlab/geometry-of-intelligence/blob/5f45eee29afa3c7507eb9a56bb132ccb92260e68/ILab/MathematicsLearning/WalkingIsomorphism.lean#L76) | 3.8 | The object type Room has exactly two elements |

The formalization is ordinary Mathlib category theory. The full notes, Synthetic Category Theory, infinity-category theory, HoTT, set-universe existence, the general Yoneda lemma, adjunction correspondence and equivalence criterion remain outside its scope. The finite equivalence carries Mathlib's additional triangle condition; it is not represented as a proof of general Theorem 3.7.

## Graph and repository publication

[Live Mathematics Learning graph](https://iontlab.org/formalization/mathematics-learning/): Mathematical Blueprint contains **15 mappings and 7 visible direct edges**. Full Lean Graph initially shows **20 authored declarations and 34 edges**; its generated-declaration toggle exposes all **73 declarations and 237 direct edges**. Curated mathematical text is independently authored metadata. All displayed dependency edges come from compiled types/values; no conceptual or shortcut edges were inserted.

- Repository: [iontlab/geometry-of-intelligence](https://github.com/iontlab/geometry-of-intelligence).
- Branch: `codex/mathematics-learning`; [implementation PR #5](https://github.com/iontlab/geometry-of-intelligence/pull/5).
- Exact verified Lean source commit: `5f45eee29afa3c7507eb9a56bb132ccb92260e68`.
- Exact deployed graph/artifact commit: `1bcff3dd09455c57d22e492cae1aa82e0e081e29`.
- This subsequent publication record adds final readback evidence; the deployed graph bytes remain those of the artifact commit above.
- All nine public graph files returned HTTP 200 and match that commit's bytes by SHA-256. [Deployment readback](deployment-readback.json) records each URL and hash.

## Regression and quality checks

- [Public readback](public-readback.json) compares the protected assets to the pre-task baseline and confirms the homepage's sole intended insertion. The nonexistent sidebar is explicitly excluded rather than mistaken for a successful raw export.
- All nine existing `math:` topic pages are accessible and retain September 22 revision dates. Protected research pages, status, conventions, roadmap, implementation references, graph assets and explanation assets are unchanged.
- The original RQ-001 compiler audit passed for all 202 declarations and reproduced `compiled.json` byte-for-byte. Its four source modules, original tools, verification evidence, graph files, toolchain and manifest have no diff from baseline `0dd880d9c66285133c44d0b3e10be2fd3d00436e`.
- Both existing RQ-001 graph modes still work: Blueprint 24 nodes/25 edges; initial Full Lean Graph 79 authored declarations/195 visible edges.
- [Wiki rendering checks](wiki-render-qa.json): all 16 new pages have no missing internal wiki links, no MathJax errors and no horizontal page overflow in the inspected browser viewport. New pages remain `[Draft]`; formal status is scoped to exact declarations.
- [Graph checks](graph-live-qa.json): both learning modes, generated visibility, module filter, declaration search and counts pass live. All 15 curated inspector presentations rendered without MathJax errors in the local pre-deployment check; the deployed files match those checked bytes. A live mathematics inspector and its pinned source links were also checked.

## Outstanding boundaries

No implementation or publication blocker remains in the delivered scope. An official public URL and republication authorization for the exact primary PDF remain unverified; no copyrighted PDF or full text extraction was uploaded. Independent human mathematical peer review is not claimed. General synthetic/higher formalizations and the future Algebra/Topology courses were not requested as completed courses and are explicitly forthcoming or outside scope. Algebra identifies Christoph Schweigert and Topology identifies Birgit Richter through verified official university links without implying endorsement.
