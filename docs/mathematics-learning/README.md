# Mathematics Learning — source and coverage metadata

The public subsection is **Higher Category Theory**. Its first learning project is **Synthetic Category Theory**. The canonical educational exposition is in [DokuWiki](https://iontlab.org/doku.php?id=mathematics_learning:start).

## Architecture retained

DokuWiki uses colon namespaces, `start` landing pages, underscore word separators, the existing `dokuwiki` template and native MathJax conventions. A configured but nonexistent sidebar is not a navigation surface. The only homepage change is one Mathematics Learning link appended to its existing Foundations Map row. Research Mathematics remains `math:start`, with its nine topic pages unchanged.

The existing seven RQ-001 explanation records and source-binding/release gates are specific to RQ-001. They are preserved. New lessons reuse their five-layer sequence, story keys, analogy limits, source attribution and explicit verification boundaries as wiki-native sections. No second explanation renderer or automatic wiki synchronization is introduced.

The existing repository and single Lake package remain authoritative for technical artifacts. New source files use `ILab.MathematicsLearning`; all four `ILab.RQ001` modules, their verification evidence, original tools, dependency manifest and toolchain are unchanged. The static graph reuses the existing viewer and the explicit Hetzner WebFTP deployment procedure; `docs/` is not an automatic deployment system.

## Source access checked before exposition

All three files were extracted from the supplied ZIP into private local storage outside the repository. Each PDF was opened, every page's text was processed, its title page was rendered and inspected, its edition/authors were checked, and its SHA-256 matched the supplied manifest. These checks confirm actual execution-environment access, not merely presence in ChatGPT Project Sources.

| Role | Supplied source | PDF pages | SHA-256 |
| --- | --- | ---: | --- |
| Binding primary | Lyne Moser and Tashi Walde, *Lecture Notes: Synthetic Category Theory* | 13 | `5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc` |
| Supplement | Denis-Charles Cisinski, Bastiaan Cnossen and Tashi Walde, *Synthetic Category Theory, Volume I: Foundations*, September 18, 2026 draft | 583 | `c58d88b027579f04aa5fd76731e2782753794c83d060a7556acf014ab4bccf31` |
| Supplement | Emily Riehl, *Category Theory in Context*, supplied second edition | 299 | `e4779f34ff0432508f1105912f39a84af3c64799b969507325c80e27c2d994dd` |

No PDFs or full extracted texts are published. The exact primary's official public PDF URL remains unverified. The [source page](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:sources) identifies official university profiles, affiliations, edition differences, rights and independent iLab authorship with AI assistance.

## Coverage

[`coverage.json`](coverage.json) accounts for all 44 numbered items (1.1–1.28, 2.1–2.7 and 3.1–3.9) plus 14 substantive unnumbered items. Each record includes source pages, original number, topic, dependencies, source-proof status, educational-layer status, formalization status and canonical public page URL. Examples within a numbered source item are covered in its linked lesson. Introductory future topics are signposts rather than additional lessons.

The eight grouped lessons each have Story / Fairy Tale, Plain Language, Mathematics, Lean and Verification sections. Their narratives, examples and proofs are independently written. The source's exercise labels are retained. Theorem 3.7 is source-stated with its proof deferred; its additional classical proof sketch is labeled independently supplied and identifies choice. Proposition 3.9's direct argument explicitly covers both target objects.

The complete educational coverage is distinct from the [selective ordinary-category formalization](../../formalization/mathematics-learning/README.md). In particular, no synthetic, HoTT or infinity-category formalization is claimed. Independent human peer review is not claimed.
