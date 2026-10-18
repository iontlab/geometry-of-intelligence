# Mathematics Learning — selected ordinary category theory

Technical companion to the [Synthetic Category Theory learning project](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:start), within [Higher Category Theory](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:start). Canonical educational prose lives in DokuWiki; this repository contains Lean sources, coverage metadata, verification evidence and the reused static graph. No automatic wiki synchronization or new deployment service is introduced.

Binding source: Lyne Moser and Tashi Walde, *Lecture Notes: Synthetic Category Theory*, supplied 13-page installment. Supplements: Cisinski–Cnossen–Walde, *Synthetic Category Theory, Volume I: Foundations* (September 18, 2026 draft, 583 PDF pages), and Emily Riehl, *Category Theory in Context* (supplied second edition, 299 PDF pages). [Source attribution and conventions](https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:sources). Source PDFs are excluded from this repository and deployment.

- [BasicCategoryTheory](../../ILab/MathematicsLearning/BasicCategoryTheory.lean): identity laws, inverse uniqueness, functor preservation, vertical naturality.
- [WalkingIsomorphism](../../ILab/MathematicsLearning/WalkingIsomorphism.lean): explicit finite categories, an adjoint equivalence, essential but not literal object surjectivity and object cardinality.
- [Complete verification record](verification/VERIFICATION.md): clean build, all-declaration audit, hashes, assumptions, reproduction and all 20 authored mappings.
- [Coverage manifest](../../docs/mathematics-learning/coverage.json): 44 numbered and 14 substantive unnumbered source items; educational coverage and Lean coverage are separate.
- [Interactive graph](https://iontlab.org/formalization/mathematics-learning/): the established RQ-001 viewer with learning data and labels. [Graph provenance](../../docs/formalization/mathematics-learning/BLUEPRINT.md).

The single existing Lake project, pinned dependencies, all four RQ-001 modules and original audit tools remain unchanged. These checks concern ordinary category theory, not a formalization of Synthetic Category Theory or all mathematical content of the notes.
