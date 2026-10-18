"""Refresh learning status pages from the source audit, never declaration totals."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[1];D=R/'docs/mathematics-learning';W=D/'wiki-current'
load=lambda p:json.loads(p.read_text(encoding='utf8'))
audit=load(D/'original/native/source-audit.json')
graph=load(R/'docs/formalization/mathematics-learning/data.json')
records=load(D/'obligations.json')['records']
registry=load(R/'docs/formalization/mathematics-learning/explanations/registry.v0.1.json')
bindings={r['source']['item_key']:r['source'] for r in registry['records'] if r['kind']=='source-item'}
base='mathematics_learning:higher_category_theory:synthetic_category_theory:'
full=audit['fully_formalized'];pending=audit['pending_eligible_items']
status=f'**{full} of 44 numbered original items are fully and faithfully formalized; 15 are affected by assigned exercises, and {pending} eligible items remain incomplete.**'
start=(W/'start.txt').read_text(encoding='utf8')
start=start.replace('reproduced in faithful facsimile excerpts','published as complete native text and typeset mathematics')
start=start.replace('Independent iLab material remains supplementary.','The original manuscript is the sole main reading content. iLab explanations are supplementary interactive layers.')
start=re.sub(r'Each lesson retains.*?A grouped lesson may cover several source items without pretending each needs a separate Lean theorem\.',
 'Each original statement has an associated Explain control. Story / Fairy Tale, Plain Language, Mathematics, Lean and Verification open as supplementary panels; Mathematics contains the exact original text. The 47 existing controls, graph and eight-chapter navigation are retained. The graph source selector also exposes 14 editorial groups of unnumbered passages; these are not additional numbered source theorems.',start,flags=re.S)
start=start.replace('Theorem 3.7 is stated in the primary notes with its proof deferred; the equivalences lesson labels its additional proof sketch accordingly.',
 'Theorem 3.7 retains the original “Proof. Next time.” Its separately checked Lean proof is available through the supplementary control.')
start=re.sub(r'\*\*The non-exercise release checks.*?Full formalization of the entire source is not claimed\.\*\*',status,start)
(W/'start.txt').write_text(start,encoding='utf8')
sources=(W/'sources.txt').read_text(encoding='utf8').replace('primary reading in facsimile excerpts','primary reading as native text, typeset mathematics and vector diagrams')
sources=sources.replace('The lesson prose, stories, additional examples and supplemental arguments are iLab educational work prepared with AI assistance.',
 'The main chapter text is the original authors’ manuscript. Story and Plain Language panels are supplementary iLab educational work prepared with AI assistance; the Mathematics panel reproduces the exact original passage.')
sources=sources.replace('Lean object and morphism universe levels are independent type-universe parameters. They do not constitute a proof that the primary\'s set-universes exist.',
 'The source-faithful layer uses actual ZFC object and hom sets in the stated set-universes, with proved bridges to Mathlib categories. Universe existence remains the authors’ explicit assumption.')
(W/'sources.txt').write_text(sources,encoding='utf8')
coverage=['====== Synthetic Category Theory — coverage and proof status ======',
 'The complete original manuscript is the main reading content of the existing eight chapters. All five explanation layers are supplementary panels. Mathematics reproduces the original statements verbatim.',status,
 'Fourteen editorial groups cover the unnumbered introduction and remarks. They are passage references, not newly invented source theorems. Compilation counts do not measure source fidelity.',
 '===== Numbered original items =====',
 '^ Source item ^ PDF pages ^ Original chapter statement ^ Exact formalization status ^']
for r in records:
    if r['kind']=='unnumbered':continue
    b=bindings[r['key']]
    coverage.append(f"| {r['kind']} {r['key']} | {', '.join(map(str,r['source_pages']))} | [[:{b['page_id']}#{b['anchor']}|Original text]] | [[https://iontlab.org/formalization/mathematics-learning/?statement={r['key']}&layer=verification|{r['formalization_status']}]] |")
coverage+=['===== Incomplete eligible items =====']
for r in audit['items']:
    if r['status']=='pending':coverage.append(f"  * **{r['key']}**: {r['correspondence']}")
# Accept the audit's explicit status vocabulary without silently omitting gaps.
if len([x for x in coverage if x.startswith('  * **')])!=pending:
    coverage=coverage[:coverage.index('===== Incomplete eligible items =====')+1]
    for r in audit['items']:
        if r['status'] not in {'fully_formalized','exercise_withheld','mixed_exercise'}:
            coverage.append(f"  * **{r['key']}**: {r['correspondence']}")
coverage+=['===== Assigned exercises =====',
 'Solutions remain withheld for 1.14, 1.15, 1.17, 1.19, 1.21, 1.23, 1.24, 1.26, 1.28, 2.1, 2.2, 2.4, 2.5, the embedded opposite-invertibility step in 2.6, and 3.3. All 17 original exercise markers, author-written partial proofs and outlines remain unchanged. The mixed status of 2.6 is not counted as fully formalized.',
 '===== Later foundations =====',
 'The introduction motivates all-dimensional weak coherence, fundamental infinity-groupoids, higher identity types and the Structure Identity Principle. The supplied installment announces later axioms but does not specify the complete intended formal system. Those passages remain exact original text; no missing axioms are invented. Existing ordinary path/groupoid and equality results remain explicitly limited supporting work.',
 f'Back: [[:{base}start|Reading path]] · [[:{base}verification|Verification evidence]]']
(W/'coverage.txt').write_text('\n\n'.join(coverage)+'\n',encoding='utf8')
verification=f'''====== Source-faithful manuscript — verification ======

The mathematical specification is Lyne Moser and Tashi Walde’s complete 13-page //Lecture Notes: Synthetic Category Theory//. The original manuscript is published once as the main native reading content, with supplementary interactive explanations. Source correspondence and Lean compilation are separate checks; independent human review is not claimed.

===== Current source coverage =====

{status}

The incomplete items are 1.8, 1.10, 1.13, 1.16, 2.7 and 3.2. Their precise missing set-coded constructions and correspondence proofs are recorded in [[:{base}coverage|the coverage page]] and the [[https://iontlab.org/formalization/mathematics-learning/source-audit.json|source-to-Lean fidelity audit]]. Valid earlier type-universe mathematics is retained as independent supporting work and is not counted as a faithful formalization of different set-universe objects.

The introduction also anticipates later higher/synthetic foundations. No univalence or full higher-coherence theorem is claimed; no missing author axioms have been invented.

===== Compiler evidence =====

The clean Lean 4.34.0 build completed successfully with 8943 jobs. The compiler audit covers **449 declarations in 15 learning modules**, including **188 authored declarations**, with **1686 direct compiler-derived project dependencies**. These are implementation counts, not source coverage counts.

The only permitted foundational dependencies are ''propext'', ''Classical.choice'' and ''Quot.sound''. No admitted expressions or project-added axioms are accepted. The manuscript’s existence of the three nested set-universes remains an explicit hypothesis.

Exact checked Lean source commit: ''{graph['sourceRef']}''. Mathlib revision: ''5ed2965256430c3649e86755f9576b54eca72435''. [[:{base}sources|Source and convention distinctions]].

[[https://github.com/iontlab/geometry-of-intelligence/tree/codex/source-faithful-native-manuscript/formalization/mathematics-learning/verification|Build log, compiler audit, source hashes and declaration mappings]] · [[https://github.com/iontlab/geometry-of-intelligence/blob/codex/source-faithful-native-manuscript/docs/mathematics-learning/original/native/source-audit.json|Exact source-to-Lean correspondence and pending prerequisites]].

===== Original manuscript and interactive QA =====

All eight saved chapter sources match the reviewed native drafts byte-for-byte. The native reading projection preserves every original word, formula, punctuation mark and diagram specification; only the existing heading style is applied to statement labels. All original proofs, partial proofs, exercise markers, “Proof. Next time.”, bibliography, affiliations and the original AI-use disclosure remain.

All **47 controls passed all five layers: 235 panel checks**. The Mathematics layer displays exact original passages. Lean and Verification use the current source audit and checked signatures. The 18 deployed learning assets match their upload hashes. Native MathJax rendering has no reported formula errors in the eight chapter captures.

All **17 obsolete facsimile media URLs return HTTP 404** after verified replacement. The original PDF remains available with unchanged SHA-256 ''5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc''.

[[https://github.com/iontlab/geometry-of-intelligence/tree/codex/source-faithful-native-manuscript/docs/mathematics-learning/native-publication-evidence|Current live source, rendering, panel, asset and media-removal evidence]].

===== Teaching boundary =====

All 17 assignment markers across 15 numbered source items retain their original status. Independently generated assigned-exercise solutions are withheld from current Lean exports, panels and graph mappings. Original author-provided proof portions remain verbatim. Historical wiki revisions and Git commits remain historical records.

Back: [[:{base}coverage|Source coverage]] · [[:{base}start|Reading path]] · [[https://iontlab.org/formalization/mathematics-learning/|Interactive graph]]
'''
(W/'verification.txt').write_text(verification,encoding='utf8')
print('Prepared current start, sources, coverage and verification pages; no network writes.')
