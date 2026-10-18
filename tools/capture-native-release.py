"""Read back public DokuWiki bytes after authorized editor publication.
No network writes. Editor digests are obtained separately through the UI.
"""
from pathlib import Path
import argparse, concurrent.futures, hashlib, json, urllib.request
p=argparse.ArgumentParser();p.add_argument('--stage',choices=['transition','final'],required=True);args=p.parse_args()
R=Path(__file__).resolve().parents[1]
W=R.parent/'mathematics-learning-20261018/native-publication'
load=lambda p:json.loads(p.read_text(encoding='utf8'))
sha=lambda b:hashlib.sha256(b).hexdigest()
captures=load(W/'rendered/editor-bindings.json')
(W/'wiki').mkdir(exist_ok=True)
headings=load(W/'statement-headings.json')
(W/'wiki/statement-headings.json').write_text(json.dumps(headings),encoding='utf8')
def get(c):
    chapter=c['page_id'].split(':')[-1]
    url='https://iontlab.org/doku.php?id='+c['page_id']
    raw=urllib.request.urlopen(url+'&do=export_raw',timeout=30).read()
    prepared=(W/args.stage/f'{chapter}.txt').read_bytes()
    assert raw==prepared,chapter+' source bytes differ from reviewed draft'
    assert sha(raw)==c['raw_sha256'],chapter+' editor digest mismatch'
    html=urllib.request.urlopen(url,timeout=30).read()
    (W/'wiki'/f'{chapter}.txt').write_bytes(raw)
    (W/'rendered'/f'{chapter}.anonymous.html').write_bytes(html)
    (R/'docs/mathematics-learning/wiki-current'/f'{chapter}.txt').write_bytes(raw)
    return {'chapter':chapter,'revision':c['revision'],'raw_sha256':sha(raw),'anonymous_html_sha256':sha(html),'prepared_bytes_match':True}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(get,captures))
(W/f'{args.stage}-readback.json').write_text(json.dumps(results,indent=2)+'\n',encoding='utf8')
print(f'PASS: {len(results)} live public source files exactly match the reviewed {args.stage} edition and authenticated editor digests.')
