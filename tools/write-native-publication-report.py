"""Write the current publication record from verified evidence and the source audit."""
from pathlib import Path
import json
R=Path(__file__).resolve().parents[1];D=R/'docs/mathematics-learning';V=R/'formalization/mathematics-learning/verification'
load=lambda p:json.loads(p.read_text(encoding='utf8'))
a=load(D/'original/native/source-audit.json');g=load(R/'docs/formalization/mathematics-learning/data.json')
labels=['Orientation / Foundations','Size and Universes','Categories and Isomorphisms','Functors and Representable Functors','Natural Transformations and Functor Categories','Yoneda Lemma','Adjunctions','Equivalences of Categories']
lines=['# Native original manuscript publication — 18 October 2026',
 'The complete Moser–Walde manuscript is now native DokuWiki text, MathJax mathematics and TikZJax vector diagrams in the existing eight chapters. The original is the sole main reading content. The former independent iLab exposition has been removed from the reading flow; Story / Fairy Tale, Plain Language, Mathematics, Lean and Verification remain interactive supplementary panels beside the original passages.',
 'The original wording, notation, numbering, diagrams, proofs, partial proofs, 17 exercise markers, “Proof. Next time.”, references, affiliations and author AI-use disclosure are retained. Mathematics panels reproduce exact original passages. Statement labels use the established heading style. The eight chapter URLs, navigation and visual design are preserved.',
 '**The overall formalization goal remains incomplete:** 23 of 44 numbered items are faithfully formalized, 15 are exercise-affected, and six eligible source items require further work. Compilation totals do not establish source fidelity. Independent human review is not claimed.',
 '| Chapter | Native original | Numbered items | Fully formalized | Exercise-affected | Eligible pending |',
 '|---|---|---:|---:|---:|---:|']
for (ch,c),label in zip(a['chapter_counts'].items(),labels):
    url='https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:'+ch
    lines.append(f"| [{label}]({url}) | Complete, verified | {c['numbered_items']} | {c['fully_formalized']} | {c['exercise_withheld']} | {c['pending']} |")
lines+=['## Exact source-to-Lean coverage',
 'The [source audit](original/native/source-audit.json) records every exact numbered item, original location and text hash, faithful declarations, correspondence and remaining prerequisites. [All authored signatures and source mappings](../../formalization/mathematics-learning/verification/declaration-mapping.json) are compiler-derived. Fourteen editorial passage groups cover the unnumbered introduction and remarks; they are not additional numbered theorems.',
 'Outstanding eligible original items:']
for r in a['items']:
    if r['status'] not in {'fully_formalized','exercise_withheld','mixed_exercise'}:
        lines.append(f"- **{r['key']}** — {r['correspondence']}")
lines+=['The introduction’s all-dimensional coherence, full fundamental infinity-groupoid, higher identity types and Structure Identity Principle await the intended later foundations. No missing axioms are invented. The existing ordinary path/groupoid and equality results remain explicitly limited supporting work.',
 'Assigned solutions remain withheld for **1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded step of 2.6, and 3.3**. The original supplied portions remain verbatim. Mixed item 2.6 is not counted as fully formalized. [Exercise exclusions](exercise-exclusions.json).',
 '## Build and provenance',
 f"Checked Lean source commit: [`{g['sourceRef']}`](https://github.com/iontlab/geometry-of-intelligence/commit/{g['sourceRef']}). Branch: `codex/source-faithful-native-manuscript`. Lean 4.34.0 and Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435` are unchanged.",
 'The clean build completed with **8943 jobs**. The compiler audit covers **449 declarations in 15 modules**, including **188 authored declarations** and **1686 direct project dependencies**. The allowed foundational dependencies remain `propext`, `Classical.choice`, `Quot.sound`; no admitted expressions or project-added axioms are accepted. The source hierarchy’s existence remains an explicit assumption.',
 '[Clean build log](../../formalization/mathematics-learning/verification/expanded-clean-build.log) · [Compiler audit and source hash lock](../../formalization/mathematics-learning/verification/expanded-audit.json) · [Current audit summary](../../formalization/mathematics-learning/verification/audit-summary.json) · [Reproduction](../../formalization/mathematics-learning/verification/VERIFICATION.md).',
 '## Live publication checks',
 '- Eight public chapter sources exactly match the reviewed native drafts and authenticated editor digests. The original text projection is unchanged by heading formatting.',
 '- **47 controls × five layers = 235 successful panel checks**. All **60 distinct declaration verification deep links** exposed by the chapter panels select the corresponding audited graph entry. The theorem graph’s five layers also pass.',
 '- All 18 learning assets match the upload hashes. Current chapter captures show zero MathJax errors and zero facsimile images.',
 '- All 17 obsolete PNG URLs return HTTP 404. The current repository copies are removed. The original PDF remains unchanged at SHA-256 `5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc`.',
 '- All 14 protected RQ-001 live assets and protected repository paths remain unchanged. Existing compiler-regression evidence retains its 202-declaration baseline.',
 '[Current evidence](native-publication-evidence/) includes source readbacks, native rendering, all panel checks, asset hashes, media removal and RQ-001 regression. [Historical facsimile evidence](original-publication-evidence/) is retained as an explicitly superseded record; it does not describe the current presentation.',
 '## Rights and authorship',
 'Publication of the complete primary manuscript was explicitly authorized by the site owner. Copyright remains with the original rights holders; the repository code license and wiki-wide license do not relicense it. No author endorsement is asserted. Story and Plain Language are independently authored iLab educational explanations with AI assistance. Supplementary books remain private references.']
(D/'PUBLICATION.md').write_text('\n\n'.join(lines)+'\n',encoding='utf8')
(D/'original/README.md').write_text('''# Original manuscript

Lyne Moser and Tashi Walde, *Lecture Notes: Synthetic Category Theory*, supplied 13-page installment.

Copyright remains with the original rights holders. The repository code license and wiki-wide content license do not relicense this manuscript. Publication was explicitly authorized by the site owner; no author endorsement of supplementary material is asserted.

`moser-walde-13-pages.pdf` is the unchanged supplementary original. `native/` contains the complete verbatim native DokuWiki transcription, exact numbered-item fragments, source audit and manifest. The eight chapters display the original manuscript once, with interactive supplementary layers. All 17 former facsimile PNGs have been removed from the current publication assets after native-text verification.

The historical facsimile manifest and its validation records remain under `../original-publication-evidence/`; current evidence is under `../native-publication-evidence/`.
''',encoding='utf8')
(V/'VERIFICATION.md').write_text(f'''# Source-faithful Mathematics Learning verification

The [source audit](../../../docs/mathematics-learning/original/native/source-audit.json) is authoritative for complete original-item coverage: **23 fully formalized, 15 exercise-affected, six eligible items pending**, out of 44 numbered items. Fourteen unnumbered editorial passage groups are not additional original theorems. The overall goal remains incomplete.

Checked Lean source commit: `{g['sourceRef']}`. The clean build passed with 8943 jobs; compiler extraction records **449 declarations, 188 authored declarations, 1686 direct local dependencies, 15 modules**. Source set-universe assumptions are explicit; ordinary Mathlib support is not counted as a different source theorem. No `sorry`, project-added axiom or dependency beyond `propext`, `Classical.choice`, `Quot.sound` is accepted.

[Audit summary](audit-summary.json), [clean build](expanded-clean-build.log), [source hash lock](expanded-audit.json), [module hashes](source-hashes.json), [declaration mapping](declaration-mapping.json), [external references](mathlib-reuse.json) and [axiom lists](all-declaration-axioms.txt).

```sh
lake clean rq001
lake build
lake env lean tools/ExtractLearningGraph.lean
SOURCE_REF={g['sourceRef']} node tools/build-learning-graph.mjs
python tools/audit-source-fidelity.py
python tools/check-learning-exercise-scope.py
node tools/check-learning-release.mjs
```

The reproducible native publication tools prepare exact manuscript-only reading flows, capture public source bytes and editor-attested digests, bind explanations, and verify deployed hashes. Actual writes use the established authenticated DokuWiki/WebFTP workflow. [Current publication evidence](../../../docs/mathematics-learning/native-publication-evidence/) records 235 panel checks, source readbacks and facsimile removal. RQ-001 source, evidence, shared plugin and dependency pins are unchanged.

Original assigned-exercise solutions remain withheld. All original author-written proofs and partial proofs remain published. Higher/synthetic foundations announced for later lectures are not invented. Independent human mathematical review is not claimed. Earlier records and Git revisions describe historical releases.
''',encoding='utf8')
print('Updated current publication report and reproduction instructions; incompleteness remains explicit.')
