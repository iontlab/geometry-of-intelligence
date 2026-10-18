"""Package only the learning viewer and the approved scoped plugin extension."""
from pathlib import Path
import datetime,hashlib,json,re,sys,zipfile
root=Path(__file__).resolve().parents[1]
graph=root/'docs/formalization/mathematics-learning'
release=json.loads((graph/'explanations/release.json').read_text(encoding='utf-8'))['release']
index=graph/'index.html'
text=index.read_text(encoding='utf-8')
text=re.sub(r'((?:src|href)="(?!https?)[^"]+\.(?:js|css))(?:\?v=[^"]+)?"',lambda m:m[1]+'?v='+release+'"',text)
index.write_text(text,encoding='utf-8',newline='\n')
files=[]
for p in graph.rglob('*'):
    if p.is_file() and p.suffix in {'.html','.css','.js','.json'} and 'fixtures' not in p.parts:
        files.append((p,'public_html/formalization/mathematics-learning/'+p.relative_to(graph).as_posix()))
for name in ['action.php','learning.php']:
    files.append((root/'integrations/dokuwiki/ilabexplain'/name,'public_html/lib/plugins/ilabexplain/'+name))
out=Path(sys.argv[1]);manifest=[]
with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED) as z:
    for p,target in files:
        data=p.read_bytes();info=zipfile.ZipInfo(target,datetime.datetime.now().timetuple()[:6]);info.create_system=3;info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,data)
        manifest.append({'path':target,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)})
out.with_suffix('.manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(f'Staged {len(files)} files in {out} ({out.stat().st_size} bytes).')
