"""Record verified native publication and removal of superseded media.

Public readbacks only. The obsolete local files are removed separately with Git.
"""
from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request, urllib.error
R=Path(__file__).resolve().parents[1];D=R/'docs/mathematics-learning'
W=R.parent/'mathematics-learning-20261018/native-publication'
E=D/'native-publication-evidence';E.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text(encoding='utf8'))
write=lambda p,v:p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
old=D/'original-publication-evidence/facsimile-manifest.json'
if not old.exists():old.write_bytes((D/'original/manifest.json').read_bytes())
old_manifest=load(old)
files=[s['file'] for c in old_manifest['chapters'].values() for s in c['segments']]
assert len(files)==17
def check(name):
    url='https://iontlab.org/lib/exe/fetch.php?media=mathematics_learning:synthetic_category_theory:original:'+name
    try:
        urllib.request.urlopen(url,timeout=30)
    except urllib.error.HTTPError as e:
        assert e.code==404,(name,e.code)
        return {'file':name,'url':url,'status':404}
    raise AssertionError(name+' is still publicly available')
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:removed=list(pool.map(check,files))
pdf='https://iontlab.org/lib/exe/fetch.php?media=mathematics_learning:synthetic_category_theory:original:moser-walde-13-pages.pdf'
pdf_hash=hashlib.sha256(urllib.request.urlopen(pdf,timeout=30).read()).hexdigest()
assert pdf_hash==old_manifest['source_pdf_sha256']
write(E/'media-removal.json',{'removed':removed,'retained_pdf':pdf,'pdf_sha256':pdf_hash})
qa=load(W/'rendered/final-panel-qa.json')
assert len(qa)==235 and len({(r['chapter'],r['control']) for r in qa})==47
assert all(r['text'].strip() and r['errors']==0 for r in qa)
write(E/'panel-qa.json',[{k:r[k] for k in ['chapter','control','layer','errors','links']} for r in qa])
captures=load(W/'rendered/editor-bindings.json')
assert len(captures)==8 and all(c['facsimiles']==0 and not c['mathErrors'] for c in captures)
write(E/'native-render-qa.json',[{k:c[k] for k in ['page_id','revision','raw_sha256','mathCount','mathErrors','facsimiles']}|{'vector_diagrams':len(c['diagrams'])} for c in captures])
for source,target in [('final-readback.json','source-readback.json'),('rendered/live-asset-sha256.json','live-assets.json')]:
    (E/target).write_bytes((W/source).read_bytes())
status_pages=[]
for name in ['start','sources','coverage','verification']:
    path=D/'wiki-current'/f'{name}.txt'
    url='https://iontlab.org/doku.php?id=mathematics_learning:higher_category_theory:synthetic_category_theory:'+name
    raw=urllib.request.urlopen(url+'&do=export_raw',timeout=30).read()
    assert raw==path.read_text(encoding='utf8').encode(),name+' status page differs'
    path.write_bytes(raw)
    status_pages.append({'page':name,'url':url,'sha256':hashlib.sha256(raw).hexdigest(),'prepared_bytes_match':True})
write(E/'status-page-readback.json',status_pages)
native=load(D/'original/native/manifest.json')
native.update(status='Native manuscript-only edition published and verified',facsimile_removal_permitted=True,facsimiles_removed=True)
write(D/'original/native/manifest.json',native)
write(D/'original/manifest.json',{'source_pdf':'moser-walde-13-pages.pdf','source_pdf_sha256':pdf_hash,
 'authors':old_manifest['authors'],'publication_authorization':old_manifest['publication_authorization'],
 'format':native['format'],'reading_flow':native['reading_flow'],'chapters':native['chapters'],
 'native_manifest':'native/manifest.json','removed_facsimile_count':17,
 'historical_facsimile_record':'../original-publication-evidence/facsimile-manifest.json',
 'current_publication_evidence':'../native-publication-evidence/'})
print('PASS: 17 live media URLs return 404; original PDF unchanged; 235 panel checks and eight native chapter readbacks recorded.')
