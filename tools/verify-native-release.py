"""Verify deployed public learning assets against the reviewed upload manifest."""
from pathlib import Path
import concurrent.futures, hashlib, json, urllib.request
R=Path(__file__).resolve().parents[1]
W=R.parent/'mathematics-learning-20261018/native-publication'
release=json.loads((R/'docs/formalization/mathematics-learning/explanations/release.json').read_text())['release']
files=json.loads((W/(release+'-files.json')).read_text())
def check(row):
    url='https://iontlab.org/'+row['path'].removeprefix('public_html/')
    data=urllib.request.urlopen(url,timeout=30).read()
    actual=hashlib.sha256(data).hexdigest()
    assert actual==row['sha256'],row['path']
    return dict(row,url=url,live_sha256=actual,verified=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    result=list(pool.map(check,files))
(W/'rendered/live-asset-sha256.json').write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS: all {len(result)} public assets exactly match the uploaded {release} package.')
