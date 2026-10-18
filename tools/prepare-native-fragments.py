"""Prepare exact source fragments for the existing Mathematics panels.

Numbered items are source units; the fourteen unnumbered keys are editorial
passage groupings inherited from the existing interface, not extra theorems.
No source text is paraphrased. TikZ vectors come from the site's checked preview.
"""
from pathlib import Path
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT/'docs/mathematics-learning/original/native'
OUT = ROOT.parent/'mathematics-learning-20261018/native-publication'
items = json.loads((NATIVE/'items.json').read_text(encoding='utf8'))
chapters = {p.stem:p.read_text(encoding='utf8') for p in NATIVE.glob('*.txt')}
def between(chapter, begin, end):
    s = chapters[chapter]
    a = s.index(begin)
    return s[a:s.index(end,a) if end else len(s)].strip()
parts = {
 'intro.what': ('foundations','Informally,','A motivating example'),
 'intro.paths': ('foundations','A motivating example','==== Axiomatic approach'),
 'intro.models': ('foundations','Traditionally,','//Homotopy type theory.//'),
 'intro.hott': ('foundations','//Homotopy type theory.//','//The structure identity principle.//'),
 'intro.sip': ('foundations','//The structure identity principle.//','//Synthetic category theory.//'),
 'intro.synthetic': ('foundations','//Synthetic category theory.//','==== Course overview'),
 'intro.course': ('foundations','We will begin','//AI-use disclosure.//'),
 'strict.motivation': ('foundations','In this first part,','==== 1. First definitions'),
 'equivalences.motivation': ('adjunctions','==== 3. Adjunctions and equivalences ====','==== 3.1. Adjunctions ===='),
 '3.5.adjoint_upgrade': ('equivalences','Fact: every equivalence','**Definition 3.6.'),
}
for key, base in [('intro.higher_morphisms','intro.what'),('intro.invertibility','intro.what'),
                  ('intro.groupoids','intro.paths'),('intro.identity','intro.hott')]:
    parts[key] = parts[base]
unnumbered = []
for key,(chapter,start,end) in parts.items():
    s = between(chapter,start,end)
    unnumbered.append({'key':key,'chapter':chapter,'verbatim_dokuwiki':s,
      'sha256':hashlib.sha256(s.encode()).hexdigest(),'status':'Editorial passage grouping; not an additional numbered source item'})
(NATIVE/'unnumbered.json').write_text(json.dumps(unnumbered,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
vectors = {}
for chapter,s in chapters.items():
    diagrams = re.findall(r'<tikzjax>[\s\S]*?</tikzjax>',s)
    if not diagrams: continue
    preview=json.loads((OUT/'rendered'/f'preview-{chapter}.json').read_text(encoding='utf8'))
    assert len(preview['diagrams']) >= len(diagrams)
    for src,svg in zip(diagrams,preview['diagrams']):
        assert '<svg' in svg and '<script' not in svg and '<animate' not in svg
        vectors[src]=svg
all_items = items+unnumbered
for item in all_items:
    diagrams=[]
    def placeholder(m):
        diagrams.append(vectors[m[0]])
        return f'ILABNATIVEDIAGRAM{len(diagrams)-1}TOKEN'
    item['render_source']=re.sub(r'<tikzjax>[\s\S]*?</tikzjax>',placeholder,item['verbatim_dokuwiki'])
    item['diagrams']=diagrams
(OUT/'render-input.json').write_text(json.dumps(all_items,ensure_ascii=False),encoding='utf8')
print(f'Prepared {len(items)} numbered items and {len(unnumbered)} editorial source passage groups.')
