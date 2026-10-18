"""Stage the source transcription in the existing eight chapters, without network writes.

The transition edition retains every facsimile until live native-text QA succeeds.
The final edition removes those blocks only. The original manuscript is the
sole reading flow; the five explanation layers live in the existing controls.
"""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / 'docs/mathematics-learning'
NATIVE = DOC / 'original/native'
OUT = ROOT.parent / 'mathematics-learning-20261018/native-publication'
CHAPTERS = ['foundations', 'size', 'categories', 'functors',
            'natural_transformations', 'yoneda', 'adjunctions', 'equivalences']
sha = lambda b: hashlib.sha256(b).hexdigest()
PDF_HASH = '5d773c2492817fbc366d7fe31fbac096dadadf2c3d24f616684a50b089f144bc'
assert sha((DOC/'original/moser-walde-13-pages.pdf').read_bytes()) == PDF_HASH
for stage in ['before', 'transition', 'final', 'rendered']:
    (OUT/stage).mkdir(parents=True, exist_ok=True)

label = re.compile(r'^(?:\*\*|//)(Definition|Remark|Convention|Example|Proposition|Construction|Theorem|Corollary) (\d+\.\d+)(?:\.\*\*|\.//|\*\*)', re.M)
coverage = json.loads((DOC/'coverage.json').read_text(encoding='utf8'))['records']
items = []
anchors = {}
intro_headings = {
 'intro.what': 'What is an ∞-category?',
 'intro.higher_morphisms': 'What is an ∞-category?',
 'intro.invertibility': 'What is an ∞-category?',
 'intro.paths': 'A motivating example comes from topology.',
 'intro.groupoids': 'A motivating example comes from topology.',
 'intro.models': 'Axiomatic approach to ∞-categories',
 'intro.hott': 'Homotopy type theory.', 'intro.identity': 'Homotopy type theory.',
 'intro.sip': 'The structure identity principle.',
 'intro.synthetic': 'Synthetic category theory.', 'intro.course': 'Course overview',
 'strict.motivation': 'I. Strict category theory',
 'equivalences.motivation': '3.2. Equivalences of strict categories',
 '3.5.adjoint_upgrade': 'Example 3.5.'}
seed = json.loads((ROOT/'docs/formalization/mathematics-learning/explanations/registry.v0.1.json').read_text(encoding='utf8'))
old_anchors = {r['source']['item_key']:r['source'].get('legacy_anchor',r['source']['anchor'])
               for r in seed['records'] if r['kind']=='source-item'}
manifest = {'source_pdf_sha256': PDF_HASH, 'status': 'prepared; live verification pending',
            'format': 'Native DokuWiki text, MathJax mathematics and TikZJax vector diagrams',
            'authoritative_files': [], 'chapters': {}, 'facsimile_removal_permitted': False}

for chapter in CHAPTERS:
    source = (NATIVE/f'{chapter}.txt').read_text(encoding='utf8')
    matches = list(label.finditer(source))
    chapter_items = {}
    for i, m in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else len(source)
        snippet = source[m.start():end].strip()
        # Bibliography follows the last mathematical item.
        snippet = snippet.split('\n==== References ====')[0].rstrip()
        key = m[2]
        row = next(r for r in coverage if r['key'] == key)
        proof = snippet.split('//Proof.//', 1)
        item = {'key': key, 'kind': m[1], 'chapter': chapter,
                'source_pages': row['source_pages'], 'source_pdf_sha256': PDF_HASH,
                'native_source': f'original/native/{chapter}.txt',
                'source_line': source[:m.start()].count('\n')+1,
                'verbatim_dokuwiki': snippet, 'sha256': sha(snippet.encode()),
                'statement_dokuwiki': proof[0].strip(),
                'proof_dokuwiki': '//Proof.//'+proof[1] if len(proof)>1 else '',
                'exercise_markers': snippet.count('Exercise'),
                'next_time_markers': snippet.count('Next time.')}
        items.append(item); chapter_items[key] = item

    original_path = OUT/'before'/f'{chapter}.txt'
    if not original_path.exists():
        original_path.write_bytes((DOC/'wiki-current'/f'{chapter}.txt').read_bytes())
    old = original_path.read_text(encoding='utf8')
    assert old.count('===== Original lecture notes — primary reading =====') == 1
    assert old.count('===== Supplementary iLab explanations =====') == 1
    head, rest = old.split('===== Original lecture notes — primary reading =====', 1)
    primary, supplement = rest.split('===== Supplementary iLab explanations =====', 1)
    preface = primary.split('**Original PDF page', 1)[0]
    preface = preface.replace('The facsimiles below reproduce', 'The native text below reproduces')
    preface = preface.replace('The iLab Story, Plain Language, Mathematics, Lean and Verification sections below are supplementary.',
        'The Explain controls beside the original passages open the supplementary Story / Fairy Tale, Plain Language, Mathematics, Lean and Verification layers. Mathematics reproduces the exact original statement.')
    preface = re.sub(r'^\[\[#story_fairy_tale[^\n]+\n', '', preface, flags=re.M)
    # Keep the old image blocks until the complete replacement is verified live.
    facsimiles = '**Original PDF page'+primary.split('**Original PDF page', 1)[1]
    # Promote only words already present in the original to the existing heading
    # style. This creates a single statement target, with no repeated exposition.
    reading = source
    for key, item in chapter_items.items():
        pattern = r'^(?:\*\*|//)'+re.escape(item['kind']+' '+key)+r'(?:\.\*\*|\.//|\*\* \([^\n]+?\)\*\*\.\*\*)'
        match = re.search(pattern, reading, re.M)
        assert match, key
        title = match[0].replace('**','').replace('//','')
        reading = reading[:match.start()]+'==== '+title+' ====\n\n'+reading[match.end():].lstrip(' ')
        anchors[key] = {'heading_text':title,'inline':True,'legacy_anchor':old_anchors[key]}
    if chapter == 'foundations':
        for text in ['A motivating example comes from topology.', 'Homotopy type theory.',
                     'The structure identity principle.', 'Synthetic category theory.']:
            original = text if text.startswith('A motivating') else '//'+text+'//'
            assert reading.count(original) == 1
            reading = reading.replace(original+' ', '==== '+text+' ====\n\n')
    # Formatting may change, but not a word, symbol, punctuation mark or diagram.
    def lexical(text):
        text = re.sub(r'^={4} (.*?) ={4}$', r'\1', text, flags=re.M)
        return re.sub(r'\s+', '', text.replace('**','').replace('//',''))
    assert lexical(reading) == lexical(source), chapter+' original reading text changed'
    navigation = old.rstrip().split('\n')[-1]+'\n'
    assert navigation.startswith(('Next:','Return:'))
    native_primary = '===== Original lecture notes — primary reading ====='+preface+reading+'\n\n'
    final = head+native_primary+navigation
    transition = head+native_primary+'**Facsimile reference retained during native-text verification.**\n\n'+facsimiles+navigation
    assert not re.search(r'^={4,5} (Story|Plain Language|Mathematics|Lean|Verification|Supplementary iLab)', final, re.M)
    assert len(list(label.finditer(final))) == 0
    for stage, text in [('transition', transition), ('final', final)]:
        (OUT/stage/f'{chapter}.txt').write_text(text, encoding='utf8', newline='\n')
    assert not re.search(r'\{\{[^}]*original:p\d+[^}]*\.png', final)
    assert len(re.findall(r'\{\{[^}]*original:p\d+[^}]*\.png', transition)) == len(re.findall(r'\{\{[^}]*original:p\d+[^}]*\.png', old))
    manifest['chapters'][chapter] = {'native_sha256': sha(source.encode()),
        'source_items': list(chapter_items), 'source_before_sha256': sha(old.encode()),
        'transition_sha256': sha(transition.encode()), 'final_sha256': sha(final.encode()),
        'vector_diagrams': source.count('<tikzjax>')}
    manifest['authoritative_files'].append(f'original/native/{chapter}.txt')

for key, heading in intro_headings.items():
    anchors[key] = {'heading_text':heading,'inline':key in {'intro.paths','intro.sip','3.5.adjoint_upgrade'},
                    'legacy_anchor':old_anchors[key]}
assert len(anchors) == 58 and sum(x['inline'] for x in anchors.values()) == 47
(OUT/'statement-headings.json').write_text(json.dumps(anchors,ensure_ascii=False,indent=2)+'\n',encoding='utf8')

assert len(items) == 44
assert sum(i['exercise_markers'] for i in items) == 17
assert sum(bool(i['exercise_markers']) for i in items) == 15
assert sum(i['next_time_markers'] for i in items) == 1
manifest['numbered_items'] = len(items)
manifest['exercise_markers'] = 17
manifest['exercise_affected_items'] = 15
manifest['reading_flow'] = 'Original manuscript only; all five supplementary layers are interactive panels.'
manifest['original_text_projection_verified'] = True
(NATIVE/'items.json').write_text(json.dumps(items, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
(NATIVE/'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
print('Prepared eight transition/final chapters; 44 exact source item blocks; 17 exercise markers; 15 exercise-affected items. No live changes or facsimile deletion.')
