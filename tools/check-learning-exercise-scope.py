"""Publication boundary for the source's explicitly assigned exercise solutions.

This checks known exclusions and exact mapping gates. It supplements, and does
not replace, the manual audit of the complete 13-page primary source.
"""
from pathlib import Path
import json, re

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / 'docs/mathematics-learning'
GRAPH = ROOT / 'docs/formalization/mathematics-learning'

def load(path):
    return json.loads(path.read_text(encoding='utf-8'))

manifest = load(DOCS / 'exercise-exclusions.json')
assigned = {a['item'] for a in manifest['assignments']}
assert assigned == {'1.14','1.15','1.17','1.19','1.21','1.23','1.24','1.26',
                    '1.28','2.1','2.2','2.4','2.5','2.6','3.3'}
assert sum(a['occurrences'] for a in manifest['assignments']) == 17
assert manifest['pages_audited'] == list(range(1, 14))
denied = set(manifest['withheld_authored_declarations'])

def forbidden(name):
    return any(name == d or name.startswith(d + '.') for d in denied)

for path in (ROOT / 'ILab/MathematicsLearning').glob('*.lean'):
    scopes=[]
    for line in path.read_text(encoding='utf-8').splitlines():
        ns=re.match(r'^namespace\s+([\w.]+)',line)
        if ns:
            scopes.append(ns[1]);continue
        if re.match(r'^(?:noncomputable\s+)?section(?:\s|$)',line):
            scopes.append('');continue
        if re.match(r'^end(?:\s|$)',line):
            scopes.pop();continue
        declaration=re.match(r'^(?:@\[[^\n]*?\]\s*)?(?:(?:private|noncomputable)\s+)*(?:structure|inductive|def|abbrev|instance|theorem|lemma)\s+([\w.]+)',line)
        if declaration:
            name='.'.join([s for s in scopes if s]+[declaration[1]])
            assert not forbidden(name), (path, name)

nodes = load(GRAPH / 'compiled.json')
assert not any(forbidden(n['id']) for n in nodes)
assert not any(forbidden(d) for n in nodes for d in n['dependencies'])
records = load(DOCS / 'obligations.json')['records']
assert len(records) == 58
for r in records:
    if r['key'] in assigned - {'2.6'}:
        assert not r['lean_declarations'], r['key']
        assert all(o['status'] == 'assigned exercise solution withheld' and not o['declarations'] for o in r['obligations']), r['key']
        assert 'solution withheld' in r['proof'].lower(), r['key']
    if r['key'] == '2.6':
        assert r['obligations'][-1]['status'] == 'assigned exercise solution withheld'
        assert not r['obligations'][-1]['declarations']
    assert not any(forbidden(n) for n in r['lean_declarations'])

registry = load(GRAPH / 'explanations/registry.v0.1.json')
for record in registry['records']:
    mapping = record['formal_mapping']
    assert not forbidden(mapping.get('declaration', ''))
    assert not any(forbidden(n) for n in mapping.get('declarations', []))
    assert mapping.get('result_key') not in {'functor','naturality','components'}

print(f'PASS: all 13 pages tracked; 17 assignments / 15 items; {len(denied)} withheld authored exports absent; {len(nodes)} compiled declarations and 58 source records respect the exercise boundary.')
