"""Preserve PR14 partial source and compiler evidence while allowing scoped later repairs."""
from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[1];BASE='1cd4fe15b242ed59a7dc2c5d3e155405355b49df'
G='docs/formalization/mathematics-learning/'
read=lambda p:json.loads((R/p).read_text(encoding='utf-8'))
old=lambda p:json.loads(subprocess.check_output(['git','show',BASE+':'+p],cwd=R))
p='ILab/MathematicsLearning/YonedaConstruction.lean'
assert (R/p).read_bytes()==subprocess.check_output(['git','show',BASE+':'+p],cwd=R)
module='ILab.MathematicsLearning.YonedaConstruction'
a=[n for n in old(G+'compiled.json') if n['module']==module];b=[n for n in read(G+'compiled.json') if n['module']==module]
assert len(a)==4 and a==b
for p,key in [('docs/mathematics-learning/obligations.json','records'),('docs/mathematics-learning/coverage.json','records'),('docs/mathematics-learning/original/native/source-audit.json','items')]:
    assert next(r for r in old(p)[key] if r['key']=='2.1')==next(r for r in read(p)[key] if r['key']=='2.1')
p=G+'explanations/registry.v0.1.json'
source=lambda reg:next(r for r in reg['records'] if r['object_key']=='explain.mathematics-learning.source.2.1')
assert source(old(p))==source(read(p))
print('PASS: PR14 source module, four declarations, partial 2.1 mappings, narratives and three open obligations unchanged.')
