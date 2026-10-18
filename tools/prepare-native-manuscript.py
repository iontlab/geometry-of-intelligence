"""Stage the source transcription in the existing eight chapters, without network writes.

The transition edition retains every facsimile until live native-text QA succeeds.
The final edition removes those blocks only. Neither edition changes navigation
or the existing five-layer headings and statement-control anchors.
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
        'The Mathematics section repeats the original source items at the existing statement controls. Story, Plain Language, Lean and Verification are supplementary iLab material.')
    # Keep the old image blocks until the complete replacement is verified live.
    facsimiles = '**Original PDF page'+primary.split('**Original PDF page', 1)[1]
    native_primary = '===== Original lecture notes — primary reading ====='+preface+source+'\n\n'
    supplementary = '===== Supplementary iLab explanations ====='+supplement
    supplementary = supplementary.replace('The following independent educational content is supplementary to the authors’ original manuscript above.',
        'Story, Plain Language, Lean and Verification below are supplementary iLab content. The numbered Mathematics items reproduce the authors’ original text.')
    # The existing Mathematics anchors now contain the exact source item too,
    # so the established controls can point to the actual original wording.
    for key, item in chapter_items.items():
        heading = f"==== {item['kind']} {key} ===="
        a = supplementary.index(heading)+len(heading)
        following = re.search(r'^={4,5} .+ ={4,5}$', supplementary[a:], re.M)
        assert following, (chapter, key)
        b = a+following.start()
        supplementary = supplementary[:a]+'\n\n'+item['verbatim_dokuwiki']+'\n\n'+supplementary[b:]
    final = head+native_primary+supplementary
    transition = head+native_primary+'**Facsimile reference retained during native-text verification.**\n\n'+facsimiles+supplementary
    for stage, text in [('transition', transition), ('final', final)]:
        (OUT/stage/f'{chapter}.txt').write_text(text, encoding='utf8', newline='\n')
    assert not re.search(r'\{\{[^}]*original:p\d+[^}]*\.png', final)
    assert len(re.findall(r'\{\{[^}]*original:p\d+[^}]*\.png', transition)) == len(re.findall(r'\{\{[^}]*original:p\d+[^}]*\.png', old))
    manifest['chapters'][chapter] = {'native_sha256': sha(source.encode()),
        'source_items': list(chapter_items), 'source_before_sha256': sha(old.encode()),
        'transition_sha256': sha(transition.encode()), 'final_sha256': sha(final.encode()),
        'vector_diagrams': source.count('<tikzjax>')}
    manifest['authoritative_files'].append(f'original/native/{chapter}.txt')

assert len(items) == 44
assert sum(i['exercise_markers'] for i in items) == 17
assert sum(bool(i['exercise_markers']) for i in items) == 15
assert sum(i['next_time_markers'] for i in items) == 1
manifest['numbered_items'] = len(items)
manifest['exercise_markers'] = 17
manifest['exercise_affected_items'] = 15
(NATIVE/'items.json').write_text(json.dumps(items, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
(NATIVE/'manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
print('Prepared eight transition/final chapters; 44 exact source item blocks; 17 exercise markers; 15 exercise-affected items. No live changes or facsimile deletion.')
